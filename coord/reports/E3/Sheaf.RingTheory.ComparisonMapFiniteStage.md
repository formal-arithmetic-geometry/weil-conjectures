## What changed

Proved `RingHom.exists_comparison_map_finite_stage` in
`Sheaf.RingTheory.ComparisonMapFiniteStage`, preserving its entire statement,
universes, visibility and existing docstring. Added two proof-only imports:
`Sheaf.RingTheory.TensorAlgebraStructureFiniteStage` and
`Sheaf.RingTheory.TensorRightFactorFiniteStage`.

Both new modules contain complete proofs. The first descends the coefficient
structure using a finite polynomial presentation of P over Z. The second
transports that structure to an upper tail, descends a finite polynomial
presentation of Q over P, and checks its scalar identity. The original theorem
restricts g to Q, derives its scalar compatibility, applies these two results,
constructs ψ with `Algebra.TensorProduct.productMap`, and proves both required
identities with tensor extensionality. This is a proof, not a decomposition
leaving new holes.

The helpers use the already proved
`TensorProduct.directedColimitBaseChangeElementwise` for representatives and
eventual vanishing. Transition identities are proved by tensor induction.
Finite upper bounds and polynomial evaluation descend the finite generators
and relations directly, avoiding construction of categorical tensor colimits.
All constructions are actual ring maps, not data from unproved existence.

## Proved and sorry left

Closed the original hole:
`RingHom.exists_comparison_map_finite_stage`
(node `lem-weil-pbc-comparison-map-finite-stage`).

Also proved the two new declarations:

- `RingHom.exists_tensor_algebra_structure_finite_stage`
  (`lem-weil-pbc-tensor-algebra-structure-finite-stage`).
- `RingHom.exists_tensor_right_factor_finite_stage`
  (`lem-weil-pbc-tensor-right-factor-finite-stage`).

No sorry remains in any delivered module. No sorry was added: one original
hole closed, zero holes split off. All three modules compile individually and
in import order through lcompile.py. The delivery dry run also performs the
axiom probe and static preflight.

Edge cases: i₀ (and j for the second helper) supplies a nonempty upper tail.
`Finset.exists_le` therefore handles empty variable and relation sets. Nothing
assumes the rings or tensor products are nonzero, φ₀ finitely presented, or a
canonical map injective. The independent universes v, w, x and y are retained.

## No longer needed

The planned dependency
`lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit`, whose
Mathlib attachment is
`RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit` in
`Mathlib.Algebra.Category.Ring.FinitePresentation`, is not needed on this proof
route. The concrete finite polynomial presentation argument avoids its
single-universe categorical interface and avoids constructing ring colimit
cocones for the tensor diagrams. No import of that module was added.

No existing import was removed: the three original public imports support the
unchanged statement. The base-change elementwise dependency remains needed
through the two new helpers; the tensor pushout universal-property dependency
remains used for assembly and extensionality. No blueprint unit statement or
realized step was bypassed. No other node or module is pruned by this proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the statement was found. The old plan was valid but
its tensor-ring-colimit construction was unnecessary. A direct finite-generator
and finite-relation argument suffices. The DAG proof and dependencies now
record the two fully proved components and tensor assembly.

The cited Stacks source files are absent locally. Tags 00QO, 00DD and 02JO were
read online, including 00QO's explicit finite-presentation proof and 02JO (3)'s
construction of Ψ. The helper proofs follow that generator/relation argument.
LeanFinder returned component results, including the categorical factorization
lemma; grep confirmed its signature and the polynomial/lift machinery.
LeanSearch returned Internal Server Error and was recorded as unavailable.
The whole-blueprint searches for tensor colimit, 00QO, algebra structure and
factor through found no blueprint statement matching either helper.

## New nodes

`lem-weil-pbc-tensor-algebra-structure-finite-stage`, in
`dag/nodes/sec-proper-base-change/`, records the proved descent of P's algebra
structure at a tensor stage. Its source is Stacks 00QO, the implication from
finite presentation to factorization, with the elementwise tensor-colimit
lemma for representatives and vanishing. Its new Lean module is
`Sheaf.RingTheory.TensorAlgebraStructureFiniteStage`.

`lem-weil-pbc-tensor-right-factor-finite-stage`, in the same chapter, records
the proved descent of Q → C after a stage structure for P has been supplied.
It includes the scalar compatibility and factorization identities, and does
not claim a tensor comparison ψ. Its source is the same finite-presentation
argument as used in Stacks 02JO (3). Its new module is
`Sheaf.RingTheory.TensorRightFactorFiniteStage`.

Both nodes retain the item's chapter and unit, point to the same blueprint
ancestor through the item, and have actual search records. No statement or
definition was changed; no change record or forced adaptation is needed.


## Second reading by E3

1. **Interfaces: pass.** Read all three delivered modules and compared the
   existing comparison module with the repository using `diff -u`. Only two
   plain proof imports and the original theorem's proof differ. Its signature,
   universes, visibility and docstring are byte for byte unchanged. The other
   two modules are new; no existing definition or statement changes and no
   change record is needed. Checked each node's recorded Lean statement against
   the actual declaration, byte for byte.
2. **Proofs and axioms: pass.** Independently compiled all three modules in
   import order with `lcompile.py --all`: clean, respectively 4.3, 9.4 and
   5.0 seconds. Compiled scratch copies with `#print axioms` for all three
   declarations: each lists exactly `propext`, `Classical.choice`, `Quot.sound`,
   with no `sorryAx`. Scanned the delivered Lean for forbidden declarations and
   `sorry`: none. Polynomial evaluations, quotient lifts and tensor maps are
   actual constructions; no data is chosen from an unproved existence theorem.
3. **New components: pass.** Both new theorems are strictly smaller components,
   fully proved, with source, complete docstring argument and matching nodes.
   The coefficient helper descends only P's action; the relative helper descends
   only Q's map after a coefficient stage has already been supplied. Neither
   restates the tensor comparison conclusion. Checked constant diagrams, zero
   rings, and empty variable/relation lists: the supplied base index makes each
   upper tail nonempty, and inserting the evaluation stage in the relation
   bound handles an empty relation list. Noninjective canonical maps are
   handled by eventual vanishing. An independent LeanFinder query, "finite
   presentation ring hom lifts to a directed system from finitely many
   generators and relations", found the categorical factorization theorem and
   ring direct-limit infrastructure, not an exact helper. A grep search for
   finite-presentation lifts/factorizations and a repository search for stage
   factorization found no existing substitute for these tensor statements.
4. **Route and pruning: pass.** Read downward from comparison assembly through
   both finite-presentation reductions to the proved elementwise tensor lemma.
   The categorical alternative needs a constructed tensor ring colimit and a
   common ring universe (checked its Mathlib signature); it does not provide
   a shorter direct proof of these independent-universe statements. The three
   public imports in each file supply its signature; the elementwise and finite
   bound imports are proof-only, as are the comparison's helper imports.
   The old categorical factorization node is no longer used. The old elementwise
   dependency is retained transitively through both helpers, and the tensor
   pushout leaf is still used directly. Thus the pruning list accounts for all
   old proof dependencies. Read `dag/units/sk-thm-p1.json`, including `realized`:
   no unit statement or realized step is bypassed or altered. The descent
   argument matches the finite-generators/finite-relations proof in
   [Stacks 00QO](https://stacks.math.columbia.edu/tag/00QO).
5. **DAG: pass.** The existing node changes only `proof`, `proof_deps` and
   `proof_origin`. Its three steps match coefficient descent, relative right
   descent and tensor assembly. Both new nodes include the required creation,
   blueprint ancestry, source, searches and Lean records, with the original
   chapter and unit. Their proof dependencies are exactly the elementwise
   base-change node; their polynomial and transition steps are recorded in
   words. No new hole or unrecorded declaration was added.

Second reading changed only this report: added the independent checks and their
results. No repair of Lean or node files was necessary. One original hole
closed, zero holes added; both new helper theorems are proved, not split-off
open statements. Temporary axiom-probe copies were removed before delivery.
