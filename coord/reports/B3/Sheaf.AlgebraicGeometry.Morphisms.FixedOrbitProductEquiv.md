## What changed

Corrected the false unrestricted `fixed_orbit_product_equiv` by requiring an
index equivalence identifying the subgroup family with `D.stabilizer`, as recorded
in `coord/changes/fixed_orbit_product_equiv.md`. The second reader replaced the
new holed reindexing helper by a direct application of `AlgEquiv.piCongrLeft`.

Added and fully proved `equivariant_orbit_model_compatible`: evaluate on D's own
representatives and extend fixed values along transporters. Its signature is the
first worker's signature unchanged. The only existing signature change is the
explicitly recorded correction of `fixed_orbit_product_equiv`; no definition or
target changed. The forced downstream adaptation obtains and passes compatibility.

## Proved and sorry left

Item: 1 of 1 corrected statements proved, `fixed_orbit_product_equiv`.
This is a repair of a false statement, not a proof of its old unrestricted form.

Second reading closed `equivariant_orbit_model_compatible` and eliminated the
`reindex_equalizer_product` hole by removing that redundant declaration and node.
No new sorry remains anywhere in this delivery. No split-off open statement remains.
The new compatible-model theorem is fully proved, not counted as an added hole.
The downstream algebra reconstruction now depends only on the standard axioms.

Explicit axiom checks: `fixed_orbit_product_equiv`,
`equivariant_orbit_model_compatible`, and
`affine_torsor_equivariant_descent_algebra` use only `propext`, `Classical.choice`,
and `Quot.sound`. The existing geometric theorem
`affine_torsor_equivariant_descent` still additionally depends on `sorryAx` from
its unchanged geometric dependencies; this delivery adds no such dependency.

## No longer needed

The item's former proof dependency `def-sbc-affine-torsor-equivariant-algebra`
is not a proof dependency of the direct reindexing argument. Its existing public
import remains for the interface and transitive algebra infrastructure.

The forced caller no longer imports `EquivariantOrbitModel`; its compatible
replacement is proved independently. The caller's old DAG proof dependency
`lem-sbc-affine-torsor-equivariant-orbit-product` is replaced by the compatible
model and the corrected product comparison, matching the Lean proof.

Removed the first worker's new `ReindexEqualizerProduct` module, import, and node;
Mathlib already supplies its content. The compatible-model module also no longer
imports `EquivariantOrbitModel`; both remaining public imports provide objects in
its signature. No whole-library module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The old comparison quantified over arbitrary m and K without any relation to D,
and is false: trivial G, H = C = integers, d = D.m = 1 and m = 0 compare a
singleton algebra with a nontrivial algebra. The existing scratch counterexample
compiles, and its axiom check contains only the three standard axioms.

The first worker's reindexing helper was essentially the same statement as the
corrected item and unnecessarily left a hole. The compatible model's proof was
also unfinished. Both issues are resolved in this second reading. The obsolete
STATEMENT-DISPUTED marker was removed from the now corrected statement.

Source read: [Stacks Project, Tag 03SF](https://stacks.math.columbia.edu/tag/03SF).
It supplies the finite-group-set context for Galois covers, not a literal statement
of either ring calculation. The compatible-model docstring gives the full
independent algebraic argument, now checked by Lean.

## New nodes

`lem-sbc-fixed-orbit-product-equiv-compatible-model` records the fully proved
compatible orbit model. Its self-contained statement, constructive proof steps,
search records, source, Lean signature, and provenance are included. There is no
new reindexing node in the final delivery.

Change record: `coord/changes/fixed_orbit_product_equiv.md`.

## Forced adaptations

`Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorEquivariantDescent` retains every
existing declaration signature, visibility, public import, and definition.
Its proof-only model import changes to the compatible model. Its algebra lemma
binds `hcompat` and passes it to the corrected comparison. The original application
returns a function awaiting compatibility, so the following `obtain` fails with
`Tactic rcases failed ... is not an inductive datatype`. These are the only changed
proof lines. The delivery tool verifies this counterfactual against the overlay.
The corresponding algebra-reconstruction node now records those actual proof steps.

## Second reading by B3

1. Compared every delivered existing module with the repository using `diff`.
   Verdict: the sole existing signature change is the recorded compatibility
   antecedent of the false comparison. Its change record contains complete old
   and new signatures and names its sole direct user (K4). Both caller signatures
   and all definitions, instances, visibility and target statements are unchanged.
2. Compiled all three modules together in import order through `lcompile.py`:
   no errors or warnings. Scanned for forbidden declarations and sorry: none.
   Explicit `#print axioms` checks give the results above. No arbitrary data is
   chosen from an unproved existence theorem: transporters come from D's fields
   and the proved local existence fact; their nonuniqueness is handled explicitly.
3. Read the compatible-model statement binder by binder and its complete docstring
   proof. It assumes only multiplicativity of ρ; no hidden identity, finite-group,
   nontrivial-ring, or domain hypothesis is needed. At d = 0 completeness and the
   representative function force D.m = 0; the products are singleton algebras.
   A zero ring causes no difficulty. For trivial G, stabilizer fixed values are
   fixed by ρ(1), so the missing identity law is unnecessary. Mathlib searches
   via leanfinder, loogle and grep found `AlgEquiv.piCongrLeft` for reindexing,
   and related orbit/stabilizer ingredients. Repository searches found the
   existing arbitrary-representative evaluation proof, which was adapted to D;
   the existing fixed-D caller cannot be reused without circular reasoning.
   Verdict: no split-off sorry remains; the compatible model is kernel checked.
4. Read the unit `sk-prop-input-spreading` and its `realized` fields. These helper
   nodes realize no unit statement or step. The finite-orbit reconstruction route
   is retained. Verdict: direct Mathlib reindexing is the shorter route; the
   redundant new module was removed and the unused proof dependencies listed above.
5. Checked the item node, new compatible-model node, and forced caller's algebra
   node against the final Lean. Verdict: proof steps, dependency unions, provenance,
   and Lean signatures agree; the corrected item retains its statement-change
   record. No unit or chapter record is changed.

Second-reading changes: proved the compatible model; replaced the holed reindexing
helper with Mathlib; removed its module and node; removed the compatible model's
unused orbit-model import; removed the stale disputed marker; corrected the DAG
proof records, search records, and progress accounting. Retained the valid statement
repair and minimal downstream adaptation.

## Forced adaptations

### Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorEquivariantDescent
Original against changed dependencies failed:
```
/tmp/forced-adaptation-tk9795ga/lean/Sheaf/AlgebraicGeometry/Morphisms/AffineTorsorEquivariantDescent.lean:52:9: error: Tactic `rcases` failed: `x✝ : (∃ e, ∀ (k : Fin m), K k = D.stabilizer (e k)) →
  Nonempty
    (((k : Fin m) → ↥(⨅ ζ, (ρ ↑ζ).equalizer (AlgHom.id H C))) ≃ₐ[H]
      (k : Fin D.m) → ↥(⨅ ζ, (ρ ↑ζ).equalizer (AlgHom.id H C)))` is not an inductive datatype

(with the modules compiled into /tmp/forced-adaptation-tk9795ga/.lbuild) [4.4 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
