## What changed

Retain one direct proof of
`AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf` in
`Sheaf.ConstructibleSheaf.TorsorEquivariantModuleIsSheaf`, using the restricted-scalars
signature required by the companion callers. R4 explicitly holds both this module and
`Sheaf.ConstructibleSheaf.TorsorEquivariantPresheafSheaf`: the latter is now a public
compatibility import of the former, removing its duplicate theorem and private proof.
Adapt the single sheaf call in `Sheaf.ConstructibleSheaf.TorsorAssociatedModuleFull`.
No definition or target statement changes. The interface consolidation is documented in
`coord/changes/equivariantModulePresheafSheaf-duplicate.md`.

## Proved and sorry left

This is a duplicate/interface repair, not a new proof-hole closure. The baseline item's
`AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf` was already proved;
its retained implementation is proved. The adapted
`AlgebraicGeometry.Scheme.GaloisCover.associatedModuleFunctor_full` also remains proved.
Holes closed: none (0 of 0 in the baseline item). Holes added: none. Split off: none.
No `sorry` remains in any of the three delivered Lean files. The duplicate implementation
in the companion is removed, while its public theorem remains accessible by import.
The retained sheaf theorem's scratch `#print axioms` shows exactly `propext`,
`Classical.choice`, and `Quot.sound`.

## No longer needed

The companion removes its duplicated private gluing implementation and its direct imports
of `Sheaf.ConstructibleSheaf.TorsorAssociatedModule`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.ConstantSheaf`,
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, and
`Mathlib.CategoryTheory.Sites.Subsheaf`, replacing them with a public import of the retained
implementation. The item's imports and original proof dependencies are still needed;
no original item proof-dependency node is pruned. No module becomes unreachable solely
from this compatibility change. The companion node now records its use of the retained
module-sheaf node rather than a second proof or scalar-transport argument.

The companion's old direct `proof_deps`,
`def-weil-pbc-inverse-image` and `def-weil-pbc-torsor-associated-module`, are
replaced by `lem-weil-pbc-torsor-equivariant-module-is-sheaf`. The associated-module
definition remains an indirect dependency through the retained theorem; this
replacement does not claim either definition module becomes unreachable.

## Where the brief, the DAG or earlier work was wrong

The returned delivery had left a duplicate declaration in the companion even though its
change record described duplicate removal. The explicit R4 companion claim now authorizes
that interface edit; it is not described as forced. The former module-sheaf node's
statement and its Lean record differed after retaining the restricted signature; its
statement correction is now recorded, with its direct DAG citers audited. Restriction
along the coefficient ring equivalence preserves and reflects the sheaf condition, so
this consolidation does not weaken the mathematical result. The companion's proof-origin
note now describes its actual compatibility import. Earlier counts of two delivered
files are superseded: there are three changed modules, all compiled without warnings.

## Forced adaptations

`Sheaf.ConstructibleSheaf.TorsorAssociatedModuleFull` is unclaimed and has an unchanged
signature. Its original source compiles against the shared baseline but fails against the
sandbox overlay at line 96: `Application type mismatch` in
`equivariantModulePresheaf_isSheaf ℓ (↑N) c`, followed by a failed `Group ↑N` instance.
The only changed proof lines replace:

```lean
exact GrothendieckTopology.HasSheafCompose.isSheaf (J := V.smallEtaleTopology)
      (F := R) _ (c.equivariantModulePresheaf_isSheaf ℓ N)
```

with:

```lean
exact c.equivariantModulePresheaf_isSheaf ℓ P N
```

The retained theorem has explicit `P` and already supplies the restricted presheaf's
sheaf condition. The adapted source compiles. Unchanged originals of
`TorsorInvariantSections` and `TorsorSectionEvaluationBijective` compile against the
changed sandbox dependencies, so no adaptations of those modules are delivered.

## Earlier second reading (a previous round; superseded)

1. Compared all three sandbox modules with the repository versions. The item's public
   signature intentionally changes to the companion's restricted-scalars signature,
   exactly as recorded in the change record. The companion's duplicate declaration is
   retired under its explicit R4 claim and reexported from the retained module. The
   fullness theorem's signature and all other public statements/definitions are unchanged.
   Verdict: documented consolidation, no accidental statement change.
2. Compiled the three-file delivery in import order using `lcompile.py`. No warnings,
   errors, `sorry`, forbidden declarations, or hollow definitions occur. The scratch
   axiom print for the retained theorem has only the three permitted axioms. Read the
   natural isomorphism, equivariance locality argument, and limit reflection instances.
   Verdict: actual proof, with no new arbitrary witness chosen from an open existence claim.
3. No statements or holes are split off. Searched the library for equivariant sheaf
   declarations and used a fresh msearch query about equivariance, subfunctors, and
   separatedness, plus Loogle for the subsheaf criterion. The only exact duplicate is
   the companion implementation now removed. Empty schemes, zero modules, trivial groups,
   and ell=0 require no extra hypothesis in this proof. Verdict: no new lemma duplication.
4. The shortest established route is preserved: pull back the continuous-function sheaf,
   impose local equivariance with `Subfunctor.isSheaf_iff`, identify locally constant
   functions using the discrete topology, and reflect through the forgetful functor.
   Only statement-needed imports are public; proof imports in the item remain plain.
   The original proof-dependency set is retained. Inspected `dag/units/sk-thm-p1.json`:
   no realized unit statement or step is bypassed. Verdict: route and pruning agree.
5. Read both delivered nodes against the actual Lean. The module-sheaf node records the
   gluing route without self-reference; the companion node uses that retained result.
   Both Lean records give the retained signature verbatim. Added the missing documented
   statement correction and audited its direct citers. Verdict: nodes agree with Lean.

Second reading changed the companion into the explicitly claimed compatibility import,
completed the module-sheaf statement-change metadata, corrected the companion proof-origin
note, and rewrote the report/change record to describe the actual three-module delivery.
No correct proof body was rewritten.

## Forced adaptations

### Sheaf.ConstructibleSheaf.TorsorAssociatedModuleFull
Original against changed dependencies failed:
```
/tmp/forced-adaptation-k8f8m604/lean/Sheaf/ConstructibleSheaf/TorsorAssociatedModuleFull.lean:96:18: error: Application type mismatch: The argument
  c
has type
  GaloisCover.{u} (ULift.{u + 1, u} P) V
of sort `Type (u + 1)` but is expected to have type
  GaloisCover.{u + 1} (ULift.{u + 2, u + 1} ↑N) ?m.473
of sort `Type (u + 2)` in the application
  equivariantModulePresheaf_isSheaf ℓ (↑N) c
/tmp/forced-adaptation-k8f8m604/lean/Sheaf/ConstructibleSheaf/TorsorAssociatedModuleFull.lean:96:18: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Group ↑N

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.

(with the modules compiled into /tmp/forced-adaptation-k8f8m604/.lbuild) [4.1 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Second reading by R4

1. Compared every delivered Lean module with its repository version using `diff`.
   The sole public signature change is the recorded consolidation of
   `AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf` to the
   companion's existing restricted-scalars signature. The companion reexports that
   exact signature instead of declaring it twice. The fullness signature and public
   definitions are unchanged. Restriction along the ring equivalence preserves and
   reflects the sheaf condition, so neither the result nor any target is weakened.
   Verdict: no accidental visible change; the intentional change has its record.
2. Compiled all three delivered files in import order through `lcompile.py`, without
   errors or warnings. Scanned them for sorry and forbidden declarations: none.
   A fresh scratch copy printed the retained theorem's axioms as precisely propext,
   Classical.choice and Quot.sound. Read the restriction/action commutation,
   continuous-function sheaf pullback, local equivariance argument, natural
   isomorphism and forgetful-limit reflection. No arbitrary data is extracted from
   an unproved existence theorem. Verdict: valid proof and concrete definitions.
3. No statements or holes are split off. Fresh Loogle search found the already-used
   `CategoryTheory.Subfunctor.isSheaf_iff`; LeanFinder search for an equivariance
   identity local on a covering sieve supplied no shorter exact theorem. The source
   search identifies only the two implementations being consolidated. The proof
   handles empty schemes, zero modules, trivial groups and ell=0 without an added
   connectedness, primality or finite-generation hypothesis. Verdict: no new
   duplicate lemma or disguised restatement.
4. The direct continuous-function/subfunctor argument is retained. The sole public
   import in the implementation supplies its statement; the remaining imports
   supply proof tools. The compatibility module's public import supplies its
   reexport. The original item's two proof dependencies remain used, so no original
   proof-dependency node or reachable module is claimed pruned. Inspected every
   realized statement/step in `dag/units/sk-thm-p1.json`: this repair changes no unit
   route. Verdict: imports, route and pruning report agree.
5. Compared both node records with the code. The implementation node records the
   actual three-step gluing argument and the precise restricted signature; the
   companion node records the compatibility dependency on it. The statement-change
   record preserves the original statement and old proof, and its sole original
   direct citer is the fullness node. Compiled unchanged invariant-sections and
   section-evaluation callers against the sandbox overlay. Compiling the original
   fullness caller against that overlay reproduces the explicit-P type mismatch;
   the delivered two-line-to-one-line proof adaptation compiles and is necessary.
   Verdict: nodes and downstream audit agree with Lean.

Second reading changed only this report by adding the current independent checks
and explicitly naming both replaced companion proof dependencies.
No correct proof body, statement, definition, import or node was rewritten. This is
an interface/duplicate repair with holes closed 0 of 0, holes added 0, split off 0,
and no pruned module. Change record:
`coord/changes/equivariantModulePresheafSheaf-duplicate.md`.

## Forced adaptations

### Sheaf.ConstructibleSheaf.TorsorAssociatedModuleFull
Original against changed dependencies failed:
```
/tmp/forced-adaptation-tx93wwah/lean/Sheaf/ConstructibleSheaf/TorsorAssociatedModuleFull.lean:96:18: error: Application type mismatch: The argument
  c
has type
  GaloisCover.{u} (ULift.{u + 1, u} P) V
of sort `Type (u + 1)` but is expected to have type
  GaloisCover.{u + 1} (ULift.{u + 2, u + 1} ↑N) ?m.473
of sort `Type (u + 2)` in the application
  equivariantModulePresheaf_isSheaf ℓ (↑N) c
/tmp/forced-adaptation-tx93wwah/lean/Sheaf/ConstructibleSheaf/TorsorAssociatedModuleFull.lean:96:18: error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Group ↑N

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.

(with the modules compiled into /tmp/forced-adaptation-tx93wwah/.lbuild) [3.9 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
