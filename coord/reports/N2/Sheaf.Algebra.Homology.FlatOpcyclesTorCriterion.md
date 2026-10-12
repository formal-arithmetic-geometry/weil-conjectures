## What changed

Repair for reviewer X-cc891, point H10 / G1: refreshed the unchanged original
`Sheaf.AlgebraicGeometry.FlatModelFiniteFreeTruncation` source in the sandbox review
packet at `files/lean/Sheaf/AlgebraicGeometry/FlatModelFiniteFreeTruncation.lean`.
Also included the delivered criterion at
`files/lean/Sheaf/Algebra/Homology/FlatOpcyclesTorCriterion.lean`.
The importer is byte-identical to the repository original, SHA256
`b7e97a23d7deab03d56fb1623184dd96bdfcff773cc492ed87c5a8293e8bacdd`.

Reran `lcompile.py --all` on this packet's `files` directory: the delivered criterion
compiled first (1.7 s), then the unchanged importer (2.6 s), both without errors or
warnings. Separately reran `lcompile.py` on the importer: it explicitly loaded the
packet's `.lbuild` overlay, so this checks the delivered criterion, not the shared
baseline version. The importer retains its existing theorem hole and is review
material only; it is not an adapted or newly delivered module.

The previous report incorrectly implied the sandbox copy was exported to the generated
independent-review packet. `deliver3.py` exports only `lean/`, nodes, change records,
and this report; `xreview.py` archives only changed repository paths, omitting unchanged
importers. To avoid losing the required source again, the full unchanged importer is
embedded below in this exported report. The independent reader should put this exact
block at `files/lean/Sheaf/AlgebraicGeometry/FlatModelFiniteFreeTruncation.lean` in its
fresh review packet before repeating the importer compile. Do not change or deliver
that importer as a forced adaptation.

Unchanged importer source for the review packet:

```lean
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Sheaf.Algebra.Homology.FlatOpcyclesTorCriterion
import Sheaf.RingTheory.FiniteProjectiveStandardFreeCover

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- The degree-zero cokernel of the canonical quotient truncation is finite free near t.
Source: Stacks Project, Tags 0653 and 00NX.
Proof: choose an affine neighbourhood of t inside U. The cokernel of Q.d (-1) 0
is quasi-coherent and finitely presented, because both terms are finite free.
At every stalk, the bounded flat complex C has Tor amplitude [0,d]. The bounded-above
free complex Q is K-flat, so its quasi-isomorphism to C gives it the same Tor amplitude.
Tag 0653 makes the degree-zero cokernel flat at each stalk. Over the chosen affine,
the corresponding finitely presented flat module is finite projective. Tag 00NX gives
an open neighbourhood of t on which it is finite free. Restriction is exact, so this
restricted cokernel is the cokernel of the restricted differential. The degree-zero
term of Mathlib's truncGE 0 is canonically isomorphic to that cokernel; transport the
finite-free isomorphism along it. Only the open neighbourhood and rank are existential;
the complex itself is the explicit canonical truncation, not an arbitrary witness.
(blueprint: lem-pc-flat-model-finite-free-truncation-zero). -/
theorem exists_local_finiteFree_truncation_zero {T : Scheme.{u}} (U : T.Opens)
    (C Q : CochainComplex U.toScheme.Modules ℤ) (d : ℕ)
    (hCge : C.IsStrictlyGE 0) (hCle : C.IsStrictlyLE d)
    (hCflat : ∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme))
    (hQle : Q.IsStrictlyLE d)
    (hQfree : ∀ n : ℤ, ∃ r : ℕ,
      Nonempty (Q.X n ≅ SheafOfModules.free
        (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r))))
    (e : Q ⟶ C) (he : QuasiIso e) (t : T) (ht : t ∈ U) :
    ∃ (V : T.Opens) (hVU : V ≤ U), t ∈ V ∧ ∃ r : ℕ,
      Nonempty ((CochainComplex.truncGE
        (((Modules.pullback (T.homOfLE hVU)).mapHomologicalComplex _).obj Q) 0).X 0 ≅
          SheafOfModules.free
          (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
```

Proved `Module.Flat.opcycles_of_exactAt` with its existing signature unchanged. Apply
`CategoryTheory.flat_iff_tor_one_quotient_ideal` and the existing natural Tor epimorphism
`CategoryTheory.exists_epi_homology_tensor_to_tor_opcycles`. For each ideal quotient,
`CochainComplex.mapBifunctorSingle₂Iso` identifies its source complex with the termwise
tensor-right complex. Transport exactness across the inverse isomorphism, use
`ExactAt.isZero_homology`, then `Limits.IsZero.of_epi`.

Added only the proof import `WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle`.
Removed the redundant direct import `Mathlib.Algebra.Homology.Additive`, which is already
publicly imported by `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`.
Updated the existing item's DAG proof and proof origin to describe the tensor comparison.
No statement or definition was added or changed. The mechanically required record
`coord/changes/FlatOpcyclesTorCriterion-Additive-import.md` documents the redundant
public-import removal and unchanged public transitive availability for all downstream users.

## Proved and sorry left

Closed the one original hole: `Module.Flat.opcycles_of_exactAt` (node
`lem-pc-module-flat-opcycles-tor-criterion`). Holes added: none. No `sorry` remains in
any delivered module. This closes 1 of 1 original holes, without a decomposition.

The first worker's proposed hole `isZero_singleTensor_homology_of_exactAt` and its
proposed node `lem-pc-module-flat-opcycles-tor-criterion-bridge` were removed before
delivery: the comparison was already proved upstream.

The proof still uses the existing open
`CategoryTheory.exists_epi_homology_tensor_to_tor_opcycles` (node
`lem-pc-module-opcycles-tor-surjection`), which is not changed by this delivery.
A scratch-copy `#print axioms Module.Flat.opcycles_of_exactAt` returned exactly
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; the upstream
`CochainComplex.mapBifunctorSingle₂Iso` returned only the three standard axioms.
Thus the local hole is closed, but the target is not yet axiom-free globally.

## No longer needed

Removed the redundant direct import `Mathlib.Algebra.Homology.Additive`; its public
availability is retained transitively through ShortComplex.HomologicalComplex.
Both original proof dependencies remain used:
`lem-pc-module-opcycles-tor-surjection` and `lem-weil-pbc-flat-tor-ideal-criterion`.
No original DAG node or module is pruned from the target's closure.

The proposed new module `Sheaf.Algebra.Homology.SingleTensorHomologyExact` and its
bridge node were removed from the sandbox delivery, rather than introducing a new hole.

## Where the brief, the DAG or earlier work was wrong

The first worker missed the existing upstream theorem
`CochainComplex.mapBifunctorSingle₂Iso` in
`WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle`. The tensor comparison
is not definitional, but it does not need a new statement or a new hole.
The earlier bridge description also incorrectly called tensorRight N "N tensor P";
the actual model is P tensor N, with N in the second input of curriedTensor.

Second-reader searches used different wording: LeanFinder queried
"tensor product of cochain complex with module concentrated in degree zero is
isomorphic to termwise tensor complex" (only tensor-unit comparisons returned);
Loogle queried `"mapBifunctor", "single"` (graded-object comparisons returned).
Searching lean/WeilConjectures with `mapBifunctor.*[Ss]ingle`,
`[Ss]ingle.*[Mm]apBifunctor`, and `map₂.*[Ss]ingle` found the exact upstream comparison.
The msearch grep service returned no hit for `mapBifunctorSingle₂Iso`; direct source
search found it and its uses in DerivedCategory.FlatModel, and local compilation
verified its exact type and standard axioms.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered module with the repository by diff. The existing declaration
signature is byte for byte identical, as are its visibility and surrounding definitions
(there are no definitions here). Restored the original copyright, module documentation,
and full theorem docstring removed by the first worker. Verdict: unchanged statement.
2. Compiled the first worker's two files, then the repaired item and an axiom-check
scratch copy using lcompile.py. No errors or warnings. No sorry or forbidden declaration
construct remains in the delivered Lean. Axioms are as listed above; sorryAx comes from
existing dependencies, not a new hole. No data is chosen by a new definition or from an
arbitrary existence theorem. Verdict: valid proof relative to existing open dependencies.
3. The proposed bridge was a true strict intermediate statement, including for the zero
ring, zero complex, zero module, and every integer a: the single-in-degree-zero comparison
needs no boundedness or flatness assumptions. However, the upstream comparison already
proves it, so removed the bridge module and node entirely. Verdict: no split-off statement
is delivered and no new mathematical obligation remains.
4. The proof follows the original top-down Tor-surjection/ideal-quotient route, using the
proved upstream comparison and elementary exactness transport. Both original proof_deps
are used. Removed the redundant Additive import and all proposed bridge imports; the new
upstream import is proof-only. Read dag/units/sk-thm-picard-duality.json: its realized fields
are unchanged (statement and sole step are empty in the repository); this delivery replaces
no unit step or unit route. Verdict: original route kept, unused import removed.
5. Updated the existing node's second proof step and proof_origin to name the actual tensor
comparison; proof_deps remain exactly the original two nodes. No new node is needed.
The Lean and DAG both express exactness transport followed by IsZero.of_epi and the Tor
criterion. Verdict: node agrees with the proof.

Second reading changed: closed the proposed bridge hole by using an existing proved
upstream isomorphism directly, removed its module and node, removed the redundant direct
Additive import, replaced the suppressed letI with an ordinary local have instance,
restored the original documentation, and synchronized the existing DAG node and report.

The first dry run required a change record for the redundant public-import removal.
Added the record with the downstream scan and holder snapshot; no downstream adaptation
is necessary because Additive remains publicly imported transitively.

## Second reading by N2

1. Compared the delivered module with the repository version. The declaration signature
   of `Module.Flat.opcycles_of_exactAt` is byte-for-byte unchanged; only its proof and
   imports differ. Verdict: pass.
2. Compiled the delivered module with `lcompile.py` (and the packet's importer). There
   are no errors, warnings, forbidden declarations, hollow definitions, or new `sorry`s.
   The local theorem uses only the standard axioms; `sorryAx` comes solely from the
   pre-existing Tor-surjection dependency. Verdict: pass.
3. Checked the proof's tensor comparison against the upstream
   `CochainComplex.mapBifunctorSingle₂Iso`; it is a proved declaration, so no split-off
   bridge statement or node is needed. The criterion is unchanged and is true in the
   zero and quotient edge cases. Verdict: pass.
4. The proof preserves the unit route through the Tor epimorphism and ideal-quotient
   flatness criterion. Both original proof dependencies remain used; the direct
   `Mathlib.Algebra.Homology.Additive` import is redundant because it remains publicly
   reachable through `ShortComplex.HomologicalComplex`. Verdict: pass.
5. The DAG proof and proof origin now record the actual upstream tensor comparison, and
   agree with the Lean proof. No node statement or unit realization changed. Verdict:
   pass.

Changed only the theorem proof, proof-only imports, the corresponding DAG proof metadata,
and the required import change record; no declarations or definitions were changed.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered module with the repository version. The theorem signature and all
   existing public declarations are unchanged byte for byte; only proof imports and the proof
   body differ. Verdict: pass.
2. Compiled the delivered module and all sandbox modules with `lcompile.py`; no errors or
   warnings, no `sorry`, forbidden declarations, or hollow definitions occur. The proof uses
   only standard axioms locally, with `sorryAx` confined to the existing upstream Tor
   surjection dependency. Verdict: pass.
3. Checked the split-off bridge proposed by the first worker and the existing upstream
   `CochainComplex.mapBifunctorSingle₂Iso`. The bridge is unnecessary because that proved
   comparison supplies the required transport; no new statement or node is delivered.
   Verdict: pass.
4. The proof follows the unit route through the Tor epimorphism and ideal-quotient flatness
   criterion, and both original proof dependencies remain used. The direct `Additive` import
   was removed because it remains publicly available through `ShortComplex.HomologicalComplex`.
   Verdict: pass.
5. The existing DAG node's proof and proof origin name the tensor comparison used in Lean, while
   its statement and proof dependencies remain unchanged. Verdict: pass.

Changed only the theorem proof and proof-only imports, removed the unused bridge proposal, and
kept the existing change record documenting the transitive import removal. No new holes remain.
