## What changed

Proved `AlgebraicGeometry.Scheme.Modules.etaleTensorSectionsRestriction_smul` in
`Sheaf.AlgebraicGeometry.EtaleTensorSections`. The proof follows clause 1 of the existing
node: the adjunction unit is linear into pushforward (hence semilinear on sections),
and the comparison and equality-transport maps are linear. Three private, proved helpers
formalize this calculation, its equivalence to an equality of multiplication endomorphisms,
and that endomorphism equality for arbitrary left adjoints of pushforward.

The public semilinearity theorem now states the equivalent equality of additive maps.
The original pointwise specialization repeatedly exceeded the kernel checking time limit;
the map formulation compiles. `smulHom_eq_iff` proves the equivalence to the original
universally quantified pointwise conclusion. No caller uses the old signature.
The change record is `coord/changes/etale-tensor-restriction-semilinearity-map-form.md`.
All definition bodies and imports are unchanged. Local tensor transparency controls start
earlier, and a local priority controls scheme-module scalar instance elaboration.
The node proof and Lean note now describe the completed semilinearity proof.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.etaleTensorSectionsRestriction_smul`
(node `lem-sc-etale-qcoherent-presheaf-functorial`). Its semilinearity conclusion is
represented by an equivalent equality of additive maps, with the equivalence proved.

The private helpers `restrictionOfAdjunction_smul`, `smulHom_eq_iff`, and
`restrictionOfAdjunction_smulHom` are proved. Identity and composition remain proved.
No `sorry` remains in the item. No hole was added and no statement was split off.
The entire module compiles cleanly through `lcompile.py` within the 60-second limit.

## No longer needed

None. No imports, nodes or modules were pruned. The existing normalized comparison,
conjugate-unit and composition/identity arguments remain necessary, and the proof
uses the same DAG dependencies. No blueprint-unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned mathematical argument is correct. The original pointwise Lean interface
causes expensive kernel conversion of concrete tensor-section types; the equivalent
endomorphism equality avoids that conversion. The change record documents the exact
old/new signatures and the formal equivalence. The blueprint statement is unchanged.
The node's previous Lean note mentioning three remaining holes was stale: identity
and composition were already proved, and this delivery closes semilinearity.

## Second reading by E3

1. **Interfaces and data: PASS.** Compared the delivered module against the repository
   with `diff` and the declaration parser. The sole changed existing signature is
   `AlgebraicGeometry.Scheme.Modules.etaleTensorSectionsRestriction_smul`, explicitly
   declared in the report and its change record. Every other existing signature and
   every definition body is unchanged. The changed theorem has the same mathematical
   content: `smulHom_eq_iff` proves both directions between multiplication-endomorphism
   equality and universally quantified pointwise semilinearity. Its source, target,
   coefficient map and hypotheses agree with the original. `downstream.py --uses` and
   searches of both library roots find no callers outside the declaring module (197
   downstream importers). No target or definition used by a target changes. The selected
   tensor adjunction has a pinned unit, rather than an arbitrary existence witness.

2. **Proof and axioms: PASS.** Independently compiled the whole delivered module through
   `lcompile.py`: no errors or warnings, 19.3 seconds. No `sorry` or forbidden declaration
   or attribute occurs in the delivered Lean. In a scratch copy, `#print axioms` for all
   seven public declarations and the three new private helpers reports only `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The semilinearity proof uses
   the adjunction unit's module linearity into pushforward, then linearity of comparison
   and equality transport. No proof or data is assumed locally.

3. **Split statements and edge cases: PASS (none split).** There are no new public
   statements, modules, nodes or holes. Read all three proved private helpers. The
   calculation is valid for arbitrary adjoints to the given pushforward and does not
   require flatness, quasi-coherence or invertibility of the scalar. Zero scalar, unit
   scalar, zero section and zero modules cause no exception. Equality of additive maps
   implies the equation at every section by evaluation; the converse is extensionality.
   No helper merely assumes the original theorem.

4. **Route and pruning: PASS.** Re-searched Mathlib with `app_smul|smul.*comp|comp.*smul`
   and read `Hom.app_smul`, `smul_apply` and `map_comp_smul`. Also checked upstream
   `pullbackUnitApp_smul`: it is specific to abstract pullback, while the delivered proof
   already uses its underlying one-line Mathlib argument for the tensor adjunction.
   All four imports are needed: tensor pullback/adjunction, the étale category and mates
   occur in definitions or signatures; `CompositionIso` is already a plain proof import.
   No dependency or module can be pruned. The existing identity and composition proofs
   are retained. The unit `sk-prop-h2` and its `realized` record are untouched; no unit
   statement or step is bypassed. Independently tried the verbatim original pointwise
   signature in a scratch copy, evaluating the proved map equality at a section: the
   compile timed out after 60 seconds. Retaining the documented equivalent interface
   is therefore justified.

5. **DAG agreement: PASS.** Read the node and the declaration/mathlib match of every
   dependency. The six existing `proof_deps` are exactly the union of the proof steps'
   `uses`, and each remains used by the definitions or proofs. The amended clause-1
   step, `proof_origin` and Lean note describe the actual generic calculation and
   map-equation specialization. The node's mathematical statement and statement
   dependencies are unchanged. There are no new-node fields to check.

**Second-reader changes:** corrected the change record's downstream count from 194 to
197, recorded the independent pointwise timeout, and added this review. No Lean proof,
statement, definition, import or DAG field needed further repair. Closed holes: the one
original `AlgebraicGeometry.Scheme.Modules.etaleTensorSectionsRestriction_smul`.
Added holes: none; split off: none; pruned: none. This is one net hole closed, not a
one-for-one decomposition.
