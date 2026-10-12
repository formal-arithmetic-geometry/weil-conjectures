## What changed

Proved `AlgebraicGeometry.Scheme.GaloisCover.exists_action_on_finiteEtale_extension`
in the assigned module, without changing its statement or public imports. Added two proof
imports: `GenericFibreHomExtension` and `GenericFibreTorsorIdentity` in
`Sheaf.AlgebraicGeometry.Morphisms`.

The first module states unique extension of arbitrary morphisms between finite étale covers
from the generic fibre. The second proves the torsor identity from that input: it constructs
the coproduct and product base-change squares, extends the generic inverse, and verifies
both inverse identities by uniqueness. Its private `genericFibre_isIso` helper is fully proved.
The assigned proof chooses the extended maps and proves the unit and multiplication laws
by comparing extensions, retaining the reversed diagrammatic composition of the left action.

## Proved and sorry left

Proved, from the named full-faithfulness input:

- `AlgebraicGeometry.Scheme.GaloisCover.exists_action_on_finiteEtale_extension`
  (`lem-sbc-generic-fibre-action-extension`): the assigned module has zero direct sorries.
- `AlgebraicGeometry.Scheme.GaloisCover.isIso_sigmaDesc_of_genericFibre`
  (`lem-sbc-generic-fibre-torsor-identity`): the new torsor module has zero direct sorries.
- The private `genericFibre_isIso` helper: completely proved, with no direct sorry.

Exactly one sorry remains in the delivery:
`AlgebraicGeometry.Scheme.finiteEtale_genericFibre_hom_extension`
(`lem-sbc-finite-etale-generic-fibre-hom-extension`, new module
`Sheaf.AlgebraicGeometry.Morphisms.GenericFibreHomExtension`). This is a strictly separate
geometric input: its statement involves no group, action, torsor identity, or action laws.
All conclusions in the assigned theorem are assembled in Lean. The result still depends
transitively on that sorry and does not yet meet the final axiom criterion.

## No longer needed

No original imports, existing nodes, or modules are pruned. The original node had no named
proof dependencies. Its unit record has empty `realized` lists; the delivery retains the
unit's action-extension route.

The plan's separate extension of each action inverse is unnecessary: the action laws imply
invertibility, and the torsor map's inverse is extended directly. No extra nodes for action
inverses, component decompositions, or torsor-map comparison are introduced. The new full
faithfulness module imports only Mathlib; it does not import the GaloisCover library.

## Where the brief, the DAG or earlier work was wrong

The existing node marked all three proof steps non-elementary but supplied no named proof
dependencies. This delivery names the missing full-faithfulness input and formalizes the
other steps. No existing statement or definition was changed or found false.

The critical distinction is restriction to the whole fibre Cη versus restriction only to
the generic point of C: the new input's docstring explains both uses of 0BQM needed to pass
between them. Disconnected covers are included by 0BQM; no connectedness of P or Z is added.
Empty covers, the trivial group, and the empty-family case cause no exception in the
categorical proof. Smoothness plus geometrically connected fibres ensures the integral
normal situation needed by the geometric input. No section, invertible group order,
Noetherian hypothesis, compactness, or surjectivity of j is assumed.

LeanSearch was unavailable (Internal Server Error) for both new statements. LeanFinder,
Loogle, source searches, and direct reading of the relevant Mathlib declarations supplied
the available searches. The proper-henselian closed-fibre full-faithfulness node has different
hypotheses and cannot replace this generic-fibre input.

`blueprint_refs.py ancestor` returned `None` because the earlier node's `created.item` is a
module name. The new nodes record the existing node's explicit blueprint ancestor
`sbc-thm-spreading-finite-etale-galois`, with the assigned node as their `via` entry.

## New nodes

`lem-sbc-finite-etale-generic-fibre-hom-extension`: unique extension of morphisms between
arbitrary finite étale covers from Cη, following the full-faithfulness argument of Stacks
0BQM. It has a complete natural-language proof and is the sole new sorry. Edge cases checked:
empty covers have the usual unique/absent morphisms, disconnected covers are permitted,
and the identity comparison returns the unique identity extension.

`lem-sbc-generic-fibre-torsor-identity`: any over-C family compatible with Z's action has an
invertible canonical torsor map, even without assumed action laws. Proved in Lean from the
first node, universal finite coproducts and pullback universal properties; its statement
isolates the torsor conclusion rather than restating existence of an extended action.
It works for the trivial group and disconnected torsors. Both new nodes inherit the
assigned node's chapter and unit. No change records are required.

## Second reading by G3

1. **Visible interfaces — pass.** Diffed the assigned module against the repository and
checked its entire theorem signature byte for byte: unchanged. Neither a hypothesis nor
a conclusion nor an existing definition changed. The only new imports in that module
are ordinary proof imports. The other two modules and nodes are new, not modifications
of existing interfaces. Restored the original assigned theorem docstring verbatim.

2. **Kernel proofs — pass with the reported remaining hole.** All three modules compile
through `lcompile.py --all`. Separate scratch copies with `#print axioms` for all three
public theorems report exactly `propext`, `Classical.choice`, `Quot.sound`, `sorryAx`.
Read the private inverse-extension helper: both composites are proved equal to identities
by `ExistsUnique.unique`, not assumed. Scanned every delivered Lean file for forbidden
constructs and holes: exactly the named hom-extension sorry, no data definitions or
anonymous holes. This is not yet an axiom-free proof of the assigned theorem.

3. **Intermediate statements — pass.** Read Stacks 0BQM's proof and 0EYJ's proof online.
0BQM gives full faithfulness at the generic point without a Noetherian assumption. For
nonempty C, smoothness gives normality and openness; the image meets the generic point,
the smooth geometrically connected generic fibre is integral, and flatness makes it
dense. Applying 0BQM first to C and then faithfulness to Cη proves the displayed unique
extension, with precisely the two pullback comparison equations. Empty C forces all
covers empty; X empty has its unique map, while nonempty X cannot acquire a map to empty
Y over the generic fibre. Disconnected covers remain within the finite étale category.
For S a field the restriction is an isomorphism and the assertion reduces to transport.
The torsor criterion requires only compatibility: its proof builds the two base-change
squares and extends the inverse of the given torsor map. For the trivial group it becomes
the diagonal criterion; empty P or C causes no exception. Neither new statement restates
existence of an action or assumes that conclusion. Independently searched with
LeanFinder's dominant-restriction query, Loogle `"IsIso", "Sigma.desc"`, Mathlib grep
for étale faithfulness and normal extensions, and repository generic-fibre/faithfulness
searches. Dominant separated hom-ext proves uniqueness only, not existence;
`Etale.forgetFullyFaithful` concerns the forgetful functor, not restriction. The existing
proper-henselian closed-fibre theorem needs different hypotheses. No short replacement
or few-minute closure of the geometric extension hole was found.

4. **Reduction and pruning — pass.** Checked the reversed multiplication order explicitly:
ψ;(a_h;a_g) = Z.smul(h);Z.smul(g);ψ = Z.smul(gh);ψ. Both over-base and comparison
conditions are supplied to uniqueness. In the torsor proof the finite coproduct is
cartesian by universal finite coproducts; the product square is proved by lifting both
projections through hψ. Finite/étale instances supply the extension theorem's hypotheses.
All explicit imports serve signatures or the proofs; the upstream finite-coproduct
instance import is ordinary, as is the hom-extension import. There were no original
`proof_deps`, so the no-pruning list is complete. Opened
`dag/units/sk-prop-input-spreading.json`: its realized arrays are empty; the original
unit route through extension of the group action is retained. No unit step is bypassed.

5. **DAG agreement — pass after clarification.** Diffed the old action node: only
`proof`, `proof_deps`, and `proof_origin` changed. Its two dependencies name exactly the
two applied public declarations. The torsor node depends on hom-extension and describes
the cartesian comparisons and inverse identities actually proved. New nodes have source,
proof steps, searches, creation metadata, blueprint ancestry, chapter, unit and verbatim
Lean signatures. Clarified the hom-extension node's first proof step: handle C empty
before claiming that its generic fibre is nonempty; openness explains nonemptiness in
the other case. This corrects prose, not a statement or definition.

Changes: restored the existing target docstring, corrected the new node's empty-case
proof prose, and added this independent review. No proof repair was needed. The old hole
`GaloisCover.exists_action_on_finiteEtale_extension` is closed, and the new hole
`finiteEtale_genericFibre_hom_extension` is added: a decomposition, net zero holes closed.
The torsor-identity theorem and private inverse-extension helper have fully checked proof
bodies, but transitively depend on that remaining geometric hole. Temporary probes were
removed after compilation.
