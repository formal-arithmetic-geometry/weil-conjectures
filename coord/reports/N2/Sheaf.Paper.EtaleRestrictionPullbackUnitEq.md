## What changed

Proved `AlgebraicGeometry.etale_restriction_pullback_unit_eq` in
`Sheaf.Paper.EtaleRestrictionPullbackUnitEq` with its signature unchanged.
Added the proof-only import
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence` for the existing
`Etale.upperStarComp_hom_app_unit_app` theorem. Two private, fully proved helpers
specialize the pointwise restriction and composition calculations already proved
in `Sheaf.AlgebraicGeometry.EtaleChartSectionsObjectComparison` to abelian groups;
that module is not imported. The main proof follows the five-step plan: diagonal
restriction formulas, two pullback-pasting identities, the two composition unit
equations, naturality, and cancellation of the comparison isomorphisms.
Updated the item's node proof and proof_origin to describe the Lean proof;
proof_deps remain the same two existing nodes. No definitions, statements,
public imports, or other modules changed. Single-file compilation passed without
warnings in 19.6 seconds before the final comment-only cleanup.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.etale_restriction_pullback_unit_eq`
(node `lem-weil-pbc-etale-restriction-pullback-unit-eq`).
No `sorry` remains in the delivered module. No holes added or split off.
The private helpers `restriction_unit` and `composition_unit` are fully proved.
The delivery dry run also runs the maintainer's axiom probe.

## No longer needed

None. All three original public imports support the unchanged statement and its
instances. The new proof-only Coherence import supplies the composition unit law.
Both planned dependency nodes remain used:
`lem-weil-pbc-inverse-image-composition` and
`lem-weil-pbc-etale-inverse-image-restriction`. No nodes or modules are pruned.
No unit statement or realized unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The node's former proof text wrote the composite as `p ≫ g'`; the well-typed
composite is `g' ≫ p`, as already used in the Lean statement and its docstring.
The revised proof record corrects this typo. The needed pointwise glue was
already proved for module-valued sheaves in EtaleChartSectionsObjectComparison,
so no new intermediate statements or sorries were needed.
The proof does not require `IsIso ι` once `hp'` is supplied; the original
hypothesis is retained unchanged.

## Second reading by N2

1. **Visible declarations unchanged — pass.** Read the repository and sandbox
   modules in full and compared them with `diff -u`. A byte comparison of the
   existing `etale_restriction_pullback_unit_eq` signature through `:= by`
   passed: the schemes, four morphisms, hcomm, both projection equations,
   IsIso and Etale hypotheses, specified hp', all let-bound comparison maps,
   and the equality are identical. The original docstrings and public imports
   are unchanged. Only a plain proof import, two private proved helpers, local
   elaboration options and the proof were added. No definition or change record
   is added; no arbitrary existence witness is chosen.

2. **Proof and axioms — pass.** Independently compiled the delivered module
   with lcompile.py: exit 0, no warnings, 18.2 seconds. Compiled a scratch copy
   with `#print axioms AlgebraicGeometry.etale_restriction_pullback_unit_eq`:
   exactly propext, Classical.choice and Quot.sound (20.7 seconds). Searched
   the delivered Lean for sorry, axiom, unsafe, opaque, implemented_by and
   extern: none. The restriction helper evaluates
   Adjunction.unit_leftAdjointUniq_hom_app and uses naturality; the composition
   helper evaluates Etale.upperStarComp_hom_app_unit_app and uses naturality.
   Both are kernel-checked proofs, not new assumptions.

3. **Split statements and existing results — pass.** No statement is split
   off and no new hole or DAG node is introduced. Read the existing private
   helpers in EtaleChartSectionsObjectComparison: they are for ModuleCat Λ,
   so are not directly applicable to AddCommGrpCat and are not public API.
   Read the generic Coherence unit theorem and the restriction comparison
   definition in OpenImmersion.Defs; the delivery uses those existing results
   rather than restating either as an unproved theorem. Searches in lean/ for
   restriction/pullback unit compatibility found the parent theorem, which
   calls this item, and the module-valued comparison, not a shorter abelian
   theorem. The helpers require no nonempty schemes, nonzero sheaves or
   invertible psi; the diagonal and pullback projection calculations remain
   valid for identity maps and the zero sheaf.

4. **Route and pruning — pass.** Read dag/units/sk-thm-p1.json, including
   realized. This item is below its realized unit steps, and retains both
   original dependency nodes. In the main proof hδ and hσ specialize the
   restriction unit law; hχj uses hι₁ and the iotaSite equation from hι₂,
   while hχq uses the two projections of theta. The two composition-unit
   identities share gamma and hbase = g' ≫ p, with hcomm supplying the other
   factorization. Naturality moves the restrictions through the units, then
   the four explicit inverse-pair equations cancel the comparisons. This
   realizes the planned unit-side argument without replacing any unit step.
   The three original public imports supply the coefficient instances and
   the statement's restriction and inverse-image constructions; Coherence is
   needed only by the proof and is correctly a plain import. No old proof
   dependency is unused, so `No longer needed: None` is complete.

5. **DAG agreement — pass.** Compared the node JSON versions: only proof and
   proof_origin changed, within the permitted fields. The three revised
   steps describe restriction_unit, composition_unit, the two pasting
   identities, naturality and cancellation as actually written. Their uses
   have union exactly proof_deps, the same two original nodes. Read both
   dependency statements and their Lean records: restriction clause (2)
   and inverse-image-composition clauses (1) and (2) provide precisely the
   laws used. The correction from p ≫ g' to g' ≫ p is in proof text only;
   the node statement and existing Lean signature are untouched.

Second-reading changes: appended this independent review and its compilation
and axiom evidence to report.md. No proof, import, signature or node repair was
needed. One original hole closed; zero holes added; zero split off; no pruning.
