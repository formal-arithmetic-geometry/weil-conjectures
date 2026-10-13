## What changed

Proved `AlgebraicGeometry.coherentFormalModule_affine_limit_scalar_composites` in
`lean/Sheaf/AlgebraicGeometry/CoherentFormalModuleAnnihilatedLimitScalar.lean` without
changing its signature or any existing declaration. The original scalar-composite
annihilation theorem and `affineLimitModule` are unchanged.

Added proof-only imports of `Sheaf.AlgebraicGeometry.IdealPowerProductZeroAffineCover`,
`Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`,
`Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`,
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel`.

Two proved private helpers perform the affine-section transport and the projectionwise
limit calculation. The main proof obtains the levelwise reverse maps from the existing
scalar quasi-inverse theorem, uses its lifting formula and naturality clause to form a
natural transformation, and applies `lim.map`. The selected maps are uniquely determined
by their lifting formula and the existence of lifts; no arbitrary object is defined from
an unproved existence statement.

Updated the existing scalar node's proof, proof_deps, and proof_origin to record the
actual affine-section steps and the limit calculation. No unit route is bypassed.
The proof follows [Stacks Remark 0888](https://stacks.math.columbia.edu/tag/0888), whose
final paragraph was checked online because the cited local Stacks source is absent here.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.coherentFormalModule_affine_limit_scalar_composites`
(node `lem-weil-pbc-formal-annihilation-affine-limit-scalar`).

The private helpers `limit_scalar_composites` and `affine_section_annihilation` are
proved. There are no sorries left in the item and no holes added elsewhere. This is
one hole closed, zero split off, rather than a decomposition into new unproved statements.

Local compilation succeeds within the default heartbeat budget. The delivery dry run
checks compilation and the axiom probe as well.

## No longer needed

No original imports, planned nodes, or modules are pruned: the existing ring-theory
scalar quasi-inverse dependency is used. A trial direct import of
`Mathlib.Algebra.Category.ModuleCat.Limits` was removed as redundant; the required
limit API and instances are already available through the public statement imports.
The redundant added direct import of
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel` was removed during
second reading: it is publicly imported by the required cokernel module. Its
DAG dependency remains used, and no module becomes unreachable through this removal.
No completion/adic-limit identification, finite generation of the limit, or
surjectivity of its projections is needed for this scalar assertion.

## Where the brief, the DAG or earlier work was wrong

The original proof step omitted the affine-section transport required before applying
the commutative-algebra theorem. The proof now explicitly obtains quasi-coherence of
both components, their kernel and cokernel, and identifies kernel and cokernel sections
with the linear kernel and quotient. Existing library declarations suffice; no statement
correction or forced adaptation is necessary.


## Second reading by U2

1. **Visible declarations unchanged — pass.** Read the complete repository/sandbox
   diff. The existing `annihilated_of_scalar_composites` proof, `affineLimitModule`
   abbreviation, and the complete scalar theorem signature are byte-for-byte
   unchanged. Only proof imports, two private proved helpers, and the original
   theorem proof were added. No change record or forced adaptation is needed.
2. **Kernel-checked proof — pass.** Compiled the delivered module with `lcompile.py`
   without errors or warnings. A scratch copy with `#print axioms` for both public
   theorems, the abbreviation, and both private helpers reports exactly `propext`,
   `Classical.choice`, and `Quot.sound`; no `sorryAx`. Searched the delivered Lean
   for forbidden declarations and sorries: none. The selected reverse maps satisfy
   the lifting formula, and clause (a) supplies a lift for every argument, so the
   formula determines each map uniquely. No data is selected from an undetermined
   unproved existence statement.
3. **Split statements and mathematical hypotheses — pass.** No statements or holes
   were split off. Read the scalar quasi-inverse theorem's actual lifting formula,
   both composite identities, and naturality clause. Read the affine ideal-power
   criterion and affine cokernel equivalence. Coherence supplies quasi-coherence;
   the latter is supplied for both kernel and cokernel before the vanishing
   criterion is applied. Kernel annihilation is transported through the image of
   the kernel inclusion; quotient annihilation through a linear equivalence.
   Zero scalars, the zero ideal, empty affine opens, zero modules, and an isomorphism
   introduce no additional assumption: the lifting and projection arguments still
   apply. The stated `ht` is passed unchanged to the existing scalar theorem.
4. **Route and pruning — pass with one import repair.** Read Stacks Project
   [Remark 0888](https://stacks.math.columbia.edu/tag/0888), the canonical `fg` map
   and final inverse-limit paragraph. The proof uses that map's naturality and
   checks both limit composites projectionwise; it needs neither surjective limit
   projections nor a completion comparison. Searched `lean/Sheaf`, the upstream
   library, and Mathlib's ModuleCat limit APIs under scalar/composite/annihilation
   terminology. Existing scalar and affine-section results are used; no shorter
   replacement of the full assertion was found. Read `dag/units/sk-thm-p1.json`
   and its realized statement and steps: none is bypassed or altered. Removed the
   redundant direct kernel import and compiled the resulting file successfully;
   the required cokernel module publicly imports it. All other proof imports
   provide declarations used explicitly. No old proof dependency is unused.
5. **DAG agrees — pass.** Compared the node JSON with the repository version and
   read the statement/Lean declaration of every recorded proof dependency. Only
   `proof`, `proof_deps`, and `proof_origin` differ. The four steps record, in order,
   quasi-coherence, affine kernel/quotient annihilation, canonical reverse maps and
   naturality, and projectionwise limit identities. Their cited dependencies are
   exactly the recorded union. The kernel node remains a genuine proof dependency
   despite removal of its redundant direct import. There are no new nodes.

Changed during second reading: removed one redundant proof-only import and updated
this report. The mathematical proof required no repair. One original hole is closed,
zero holes are added, and zero dependency modules are pruned.
