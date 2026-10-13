## What changed

Repaired `Sheaf.Algebra.Homology.SingleSupportTorAcyclicTensor` while preserving its
public theorem signature, visibility, and public imports. The sandbox contains the
constructive projective-resolution and functorial-flat-resolution proof from the
returned delivery.

The degree-zero tensor augmentation now obtains epimorphy directly from
`Cofork.IsColimit.epi` applied to its mapped cokernel cofork. This replaces the
expensive search for tensor preservation of epimorphisms and removes both local
heartbeat increases. The reindexed tensor augmentation now composes its explicit
quasi-isomorphism proof with `quasiIso_of_isIso` using `quasiIso_comp`, avoiding the
second expensive instance search. All compiler limits remain at their defaults.

Removed the unused proof imports `Sheaf.Algebra.Homology.BoundedFlatKFlat` and
`Sheaf.Algebra.Homology.MixedTensorKFlatQuasiIso`. Updated the existing DAG node's
proof and proof dependencies to describe the constructive route actually used.

## Proved and sorry left

Closed the original single hole:
`CochainComplex.quasiIso_tensor_of_single_support_tor_acyclic`
(node `lem-pc-single-support-tor-acyclic-tensor`). The four private helper theorems
are fully proved. No sorry remains in the delivered module, and no hole is added.
This is a proof, not a decomposition into new holed statements.

The repaired module compiles with the normal limits and no warnings. The delivery
dry run additionally checks the axioms of all declarations.

## No longer needed

Removed proof imports and corresponding proof dependencies:

- `Sheaf.Algebra.Homology.BoundedFlatKFlat`, node
  `lem-pc-module-bounded-flat-kflat`: use the source-library categorical theorem
  `kFlat_of_isStrictlyLE_of_flat` directly.
- `Sheaf.Algebra.Homology.MixedTensorKFlatQuasiIso`, node
  `lem-pc-mixed-tensor-kflat-quasi-iso`: use the source-library
  `whiskerRight_of_kFlat` and the tensor-with-single natural isomorphism directly.

The common K-flat refinement in the homotopy category is unnecessary: naturality
of the functorial flat resolution gives strictly commuting comparison squares.
These removals apply to this item's proof; other items may still need the modules.

## Where the brief, the DAG or earlier work was wrong

The return reports two deterministic typeclass timeouts, both reproduced during
this repair. Raising heartbeat limits in the earlier attempted repair did not
solve the tensor epimorphism search. Both searches are now replaced by explicit
proofs. The return's importer attribution names the item itself; the actual errors
are inside its private helpers. No external importer adaptation is required:
public signatures and public imports are unchanged, and only private proof imports
were removed.

The original DAG planned a common homotopy refinement and a mixed-scalar tensor
comparison. The completed proof uses functorial flat resolutions and ordinary
tensor directly. The existing node now records this route. The unit's realized
statement and proof steps are unchanged.

## Second reading by M2

1. Compared the complete delivered Lean file and node against the repository with
   `diff`. The existing public theorem signature, visibility, and docstring are
   byte-for-byte unchanged. There are four new private proof helpers, no public
   definitions, no changed hypotheses, and no change record is needed. Verdict: pass.
2. Compiled the delivered module using lcompile.py with default limits: clean,
   no warnings. Compiled a scratch copy with `#print axioms` for the target and
   each of the four private helpers. Every declaration uses exactly `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Inspected the source:
   no sorry, axiom, unsafe, opaque, implemented_by, extern, or hollow definition.
   The chosen projective resolution and functorial flat resolution come from
   proved library constructions/instances; no data is chosen from an unproved
   existence theorem. Verdict: pass.
3. No statement was split off and no hole was added. Read all private helpers:
   degree zero uses the preserved cokernel, positive degrees use Tor vanishing,
   reindexing puts degree i at k-i, and naturality plus two-out-of-three transfers
   the comparison to the specified resolution. These arguments cover the zero
   module, arbitrary integer k, and an unbounded K-flat source; no flatness of B
   or boundedness of P was silently assumed. Verdict: pass.
4. Searched again with Lean Finder for tensor augmentation under vanishing higher
   left derived functors, and with grep for left-derived quasi-isomorphisms and
   K-flat whiskering, as well as reading related Sheaf and upstream modules.
   The relevant results are isoLeftDerivedObj and projective Tor vanishing,
   already used or insufficient for the general Tor-acyclic module. No shorter
   complete route was found. All three added proof imports are plain imports.
   Checked the existing public imports: Abelian and Projective supply instances
   used by Tor in the statement; Colimits supplies the coproduct instances used
   by the tensor-complex functor in the statement. An experiment making Colimits
   private failed at the public theorem signature, so it was restored. Both old
   proof dependencies no longer used are listed under No longer needed. Read
   dag/units/sk-thm-picard-duality.json: this node and the removed dependencies
   do not realize a unit step, and the unit route is unchanged. Verdict: pass.
5. Compared the node JSON versions. Only proof, proof_deps and proof_origin have
   changed; the recorded Lean signature still agrees exactly. The three proof
   steps describe the actual support isomorphism, projective augmentation, and
   functorial comparison. The sole remaining proof dependency is the Tor
   definition; the two removed dependencies are exactly the pruned nodes.
   No new node is required for a split-off hole. Verdict: pass.

Second reading changed only this report. The proof and node repairs were already
correct. Closed holes: CochainComplex.quasiIso_tensor_of_single_support_tor_acyclic
(one of one original holes). Added holes: none; split off: none.
