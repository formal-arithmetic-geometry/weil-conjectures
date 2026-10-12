## What changed

Reduced `AlgebraicGeometry.etaleModuleInverseImageTransport`, with its original signature,
to the existing supplied-lift module construction and linearity criterion, and two new,
strictly smaller transport lemmas. The parent proof constructs the action witnesses,
proves uniqueness of the target action by sectionwise extensionality, combines the
scalar transport and tensor comparison, and derives both unit and counit equations
from the hom-equivalence equation using a proved private categorical helper.

The new modules are `Sheaf.AlgebraicGeometry.EtaleModuleRingIsoAdjunction` and
`Sheaf.AlgebraicGeometry.EtaleModuleRingIsoTensor`. Each states one public theorem,
with a complete proof sketch, source and matching DAG node. The first assumes a
supplied module lift and its linearity criterion; it does not construct the lift or
prove the action or tensor equations. The second works for arbitrary supplied module
functors and restriction comparison; it does not construct an inverse image or an
adjunction. These are steps 2 and 3 of the original plan, rather than renamings of the
whole theorem. The node's proof and dependencies now follow the Lean reduction.

All existing public imports and signatures are preserved. Proof imports use ordinary
`import`. The main declaration uses a 600000-heartbeat bound for specializing the
abstract adjunction identities in the dependent module package; file compilation
remains below the required 60-second limit.

Sources read: the parent and dependency nodes and their Lean signatures; Mathlib's
`Sheaf/PushforwardContinuous.lean` and `Sheaf/ChangeOfRings.lean`; Stacks
[03D3](https://stacks.math.columbia.edu/tag/03D3),
[03D6](https://stacks.math.columbia.edu/tag/03D6), and
[03D7](https://stacks.math.columbia.edu/tag/03D7), and
[03CZ](https://stacks.math.columbia.edu/tag/03CZ).
The checked-in clone does not contain `literature/stacks-project/sites-modules.tex`,
so those source places were read on the Stacks website.

## Proved and sorry left

`AlgebraicGeometry.etaleModuleInverseImageTransport` has a complete Lean proof from
named statements. There is no direct `sorry` in the item's module.
Its private `adjunctionForgetUnitCounit` is also proved. In particular the parent
itself proves the stronger unique-existence action clause and the unit and counit
comparison equations; these were not left to the new statements.

Remaining sorries introduced by the delivery:

- `AlgebraicGeometry.etaleModuleRingIsoAdjunction`, node
  `lem-weil-pbc-etale-module-ring-iso-adjunction`.
- `AlgebraicGeometry.etaleModuleRingIsoTensor`, node
  `lem-weil-pbc-etale-module-ring-iso-tensor`.

The parent also depends on the existing
`AlgebraicGeometry.etaleInverseImageModuleConstruction` and
`AlgebraicGeometry.etaleInverseImageModuleLinearCriterion`. Their existing declarations
are used without copying or changing their statements; the current repository proves
both, with open dependencies below them. Consequently this is a
compiling reduction, not an assertion that the target's entire axiom closure is closed.

## No longer needed

Removed the proof imports `Sheaf.AlgebraicGeometry.EtaleInverseImageModuleAdjunction`
and `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` (the latter is already
available through the statement imports).
The parent does not need its node `lem-weil-pbc-inverse-image-module-adjunction`:
the construction and linearity criterion can both be applied directly to the supplied
`Lr`, `ar`, `er`, and `ea`. No choice of another ring lift or uniqueness-of-left-adjoints
transport is needed.

The parent no longer has direct proof dependencies on
`lem-weil-pbc-etale-inverse-image-algebraic-structures`,
`def-weil-sheaf-of-modules-category`, `def-weil-pbc-direct-image`,
`def-pur-sheaf-tensor-product`, or `def-weil-pbc-sheafification`.
These definitions remain available through the necessary public imports, and the
construction and two transport statements retain the appropriate dependencies on them.
They are not claimed globally unreachable. The ring/group lift package remains a
statement dependency of the unchanged parent, and is used by the existing construction.

No other existing import is removed: all three original public imports are needed
by the unchanged statement. The new adjunction module does not import the tensor
module; the tensor module does not import the adjunction or inverse-image construction.

## Where the brief, the DAG or earlier work was wrong

The original first step called for identifying a separately chosen ring lift with
`Lr` by uniqueness of left adjoints. The current
`etaleInverseImageModuleConstruction` already accepts every compatible supplied ring
adjunction, so that identification is unnecessary. Its ordinary sectionwise equalities
also suffice for the parent's `HEq` clauses.

The constant-ring compatibility hypothesis `hconst` is not mathematically needed
for this transport package. It is retained verbatim; no target or intermediate
statement was weakened or changed. The proof retains a reference to the supplied
hypothesis to satisfy the unused-variable linter.

The unit `sk-def-exchange` was read: this item is below its realized statement, and
none of the unit's statement or steps is bypassed. The new lemmas stay in the same
unit and chapter. Whole-blueprint searches for restriction scalars, change of rings,
and tensor isomorphism did not find this package. The topological-space
`SheafOfModules.exists_changeOfRingsAdjunction` is not a lemma for arbitrary sites and
cannot specialize to the small etale site. LeanSearch returned Internal Server Error;
this is recorded as unavailable, not as evidence of absence.

## New nodes

`lem-weil-pbc-etale-module-ring-iso-adjunction`: step-2 part of the original transport
argument, assuming the actual linearity criterion for `L0` and `e0`. Restriction along
an invertible ring map preserves the same abelian groups and transports precisely the
linear maps. The adjunct identity `hc` identifies the transported right adjoint with
the existing direct image along `gamma`. There is no tensor/action claim in this node.

`lem-weil-pbc-etale-module-ring-iso-tensor`: step-3 part of the original argument.
Its section map sends a tensor to inverse-scalar multiplication followed by `t.inv`.
The inverse is `1 tensor t.hom(n)`; balancing and the two ring inverse identities
prove both composites. Naturality and sheafification give the statement exactly.
It assumes arbitrary functors and a supplied natural restriction comparison, so it
is independent of inverse-image construction and adjunction transport.

Edge cases checked in the proof sketches: identity ring isomorphisms, zero section
rings and zero modules. The constructions use neither nonzero rings nor nonempty
sites; identity and zero cases reduce to the unit/scalar and inverse-isomorphism
identities. For an arbitrary nontrivial natural `t`, the tensor formula explicitly
includes `t.inv`, and its inverse explicitly includes `t.hom`; no identity-on-sections
assumption about `t` is added. The action uniqueness proof uses only the prescribed
sectionwise scalar equation, so it includes all admissible action witnesses.


## Second reading by F1

1. Compared all delivered modules with the repository. The only existing public
   declaration has a byte-for-byte identical signature; its public imports are
   unchanged. No definitions or target statements changed, and no change record is
   needed. The new declarations are separate modules, not alterations to an old API.
2. Compiled all three modules through lcompile.py in import order and checked the
   delivery tool's axiom probes. Only the two reported public named theorems contain
   sorry; no definition, private helper, or partial parent proof contains one. There
   are no forbidden declarations or trust overrides. The parent's axiom closure
   still includes sorryAx through the stated dependencies; this is a decomposition.
   One old hole is closed, two new holes are added, so the delivery alone has net -1
   holes before any closure-wide pruning, and does not claim a closed target.
3. Read both new signatures and their docstring arguments. The adjunction lemma
   assumes the supplied lift and linearity criterion; the tensor lemma assumes the
   comparison t and is independent of adjunction construction. Each is strictly a
   part of the original argument. Restriction along the ring inverse constructs the
   transported object explicitly in the proposed proof; no arbitrary existence
   witness defines data. Checked identity ring maps, zero rings/modules, empty-site
   cases, and nonidentity t: the tensor formula needs t.inv and the inverse needs
   t.hom, exactly as stated. Independent Loogle/LeanFinder searches and rg of the
   library found hom-equivalence identities and sectionwise scalar adjunction
   ingredients, but no ready theorem with either complete sheaf signature. Neither
   remaining hole has a short direct application proof from these ingredients.
4. The parent uses the supplied construction and criterion directly, proves action
   uniqueness by sections, and derives the unit/counit through the private generic
   adjunction lemma. The report now lists both removed proof imports and all six
   obsolete direct proof dependencies. No claim is made that these modules are
   globally unreachable. Read sk-def-exchange.realized: its statement nodes remain
   in place; this item is below them and bypasses no realized unit step. The old
   parent docstring describes the superseded uniqueness-of-left-adjoints route;
   the corrected route is recorded in this report and the DAG proof.
5. Checked the parent DAG proof against each Lean application and the two new
   node signatures against their source files. proof_deps is the union of the proof
   steps' uses. The new nodes contain sources, complete arguments, searches, Lean
   records, creation metadata, and matching unit/chapter/blueprint ancestry.

Second reading changed only the report: documented the second removed import,
updated the status of the existing construction/criterion, and explicitly counted
this delivery as one hole closed and two split off. No Lean proof or signature
needed repair.
