## What changed

Decomposed the construction into two proper parts: local lifting/cokernels, then
overlap lifting, effective descent and gluing for those specified local objects.
The original theorem assembles those parts and proves the final restriction
isomorphism, restriction quasi-coherence, invertibility of the canonical counit,
and its exact identity equation on opens. It uses the adjunction Hom bijection
and right triangle identity explicitly. The original theorem signature and every
field of EtalePresentedRecovery are unchanged.

Moved the five existing coordinate definitions verbatim into the new publicly
reexported EtalePresentedRecoveryData module so both construction obligations
can use them without an import cycle. The full recovery structure stays in the
original module. Change record:
coord/changes/H2-etale-presented-recovery-decomposition.md.

## Proved and sorry left

Original holes: 1, in
AlgebraicGeometry.Scheme.Modules.etalePresentedModule_effectiveRecovery.
That body now has a complete proof combining the two construction steps and
proving the adjunction tail. This is a decomposition, not a completed proof of
the recovery construction: zero of the original one is closed independently of
new holes. The item itself has zero sorry.

Added holes: 2, exactly the entire proofs of these public theorems:
- AlgebraicGeometry.Scheme.Modules.etalePresented_localCokernels.
- AlgebraicGeometry.Scheme.Modules.etalePresented_descentGluing.

Every added hole has a source, proof in words, new module and matching DAG node.
No definition, private helper or nested proof contains sorry. Relative textual
hole count: 1 removed, 2 added (net minus one). Validation is by lcompile.py and
the delivery preflight; all four files compiled successfully (15.6 s, 23.6 s, 20.3 s, 42.2 s).
Two style warnings from that first compile were then corrected before delivery.

## No longer needed

No mathematical node or module is claimed pruned. The item's direct proof-only
imports of WeilConjectures.AlgebraicGeometry.Descent,
WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel,
WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing and
Sheaf.AlgebraicGeometry.FpqcFinerThanEtale are removed: those ingredients belong
to the two construction obligations and remain in their DAG proof dependencies.
The original public imports are preserved transitively through the coordinate
module. All original planned mathematical dependencies remain needed in the
split construction, and no blueprint unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The dependency theorem quantifies existentially
over contexts whereas the item accepts an arbitrary context family; its contexts
contain only proof fields, so the proof identifies them by proof irrelevance.
The new local theorem needs neither a covering hypothesis nor global site
quasi-coherence: the supplied exact presentations suffice. The descent theorem
accepts the actual local datum, rather than repeating its existence conclusion.

Edge cases checked in the statements: empty basis types are free zero modules;
empty chart index is harmless for local construction and, with joint
surjectivity, forces an empty base for descent. No quasi-compactness of individual
étale chart maps is added. Arbitrary universe-w chart families remain allowed.

## New nodes

- def-trf-etale-presented-recovery-coordinates records the five unchanged,
  relocated coordinate definitions, with their existing ring maps and tensor
  transports.
- lem-trf-etale-presented-local-cokernels is precisely original DAG steps 1–2
  and the local normalized tensor coordinates. It has no overlaps or global data.
- lem-trf-etale-presented-descent-gluing is original steps 3–6 for an already
  specified local recovery datum. It has no restriction/counit conclusion.

All use Stacks Project Descent Tag 03DX, with the existing component dependency
nodes. LeanSearch, LeanFinder, Loogle, source grep and blueprint search found no
duplicate recovery construction. The unit statement and realized route stay
unchanged. No second-reader section is included for this dispatcher assignment.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
