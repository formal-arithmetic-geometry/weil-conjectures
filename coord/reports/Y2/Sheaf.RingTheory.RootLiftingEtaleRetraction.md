## What changed
Proved `IsLocalRing.existsUnique_algHom_of_monic_simple_root_lifting_etale` without
changing its statement. Added two proved private helpers for the residue map at a
rational prime and unique lifting of a standard étale residue-field map. The target
proof constructs and compares localized maps explicitly. Added the proof-only import
`Mathlib.RingTheory.Unramified.LocalStructure`. The second reader removed the
redundant quotient-operations import and made Henselian proof-only; see
`coord/changes/root-lifting-etale-retraction-proof-imports.md`.

## Proved and sorry left
Proved the item's only sorry:
`IsLocalRing.existsUnique_algHom_of_monic_simple_root_lifting_etale`.
Both private helpers are proved. No sorry remains and none is added elsewhere.
The proof uses only Mathlib, including Tags 00UE and 06RR and
`StandardEtalePair.hom_ext`, `lift`, and `HasMap.isUnit_derivative_f`.

## No longer needed
Removed the redundant `Mathlib.RingTheory.Ideal.Quotient.Operations` import added
by the first worker; made the existing Henselian import non-public. No DAG node is
pruned. The six-step DAG route and all four recorded proof dependencies are retained.
No Sheaf or WeilConjectures dependency is needed beyond the existing Mathlib leaves.

## Where the brief, the DAG or earlier work was wrong
No mathematical correction was needed. The planned elementary residue-map and
localization steps are now explicit Lean proofs. The scheme residue-field map is
handled through `Scheme.Spec.residueFieldIso`, global evaluation naturality, and the
quotient universal property, without changing any statement or definition.


## Second reading by Y2

1. Compared the sole delivered module with the repository using `diff -u`. The
   existing theorem signature, its hypotheses, conclusion, and docstring are byte
   for byte unchanged. No existing definition changed. The import visibility repair
   has the change record named above; the sole direct importer's independent public
   Henselian import preserves downstream availability.
2. Compiled the module locally without errors or warnings. A scratch copy printed
   the axioms of the public theorem and both private helpers: exactly `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. No sorry, axiom, unsafe,
   opaque, implemented_by, extern, or hollow definition occurs in the delivery.
3. No statement is split off and no new node is needed. Read both proved helpers:
   the first obtains the residue map from naturality and the quotient universal
   property; it does not assume etaleness. The second uses monicity, the standard
   etale derivative identity, root lifting, and 06RR, each with its required
   hypotheses. For a field R the lifted root is its residue root; a zero source
   algebra has no residue map, so that case is vacuous; a constant monic polynomial
   cannot admit the residue root used here. No extra restriction is introduced.
4. Read the six proof steps, all four dependency nodes and their Mathlib matches,
   and `dag/units/sk-thm-p1.json` realized. Step 1 constructs rho with kernel q and
   identifies any retraction's reduction by subtracting a lifted scalar. Step 2
   uses the recorded 00UE declaration and its finite-presentation/etale instances.
   Step 3 explicitly extends maps to the localization and compares them there.
   Steps 4 and 5 use `hasMap_X`, `HasMap.map`, `HasMap.isUnit_derivative_f`, `lift`,
   and `hom_ext` from the recorded standard-pair leaf. Step 6 applies the recorded
   06RR theorem with equal residues and a unit derivative. Searched the current
   Lean library, upstream Henselian module, and Mathlib Henselian/StandardEtale/
   LocalStructure sources; the upstream result is the converse, and no shorter
   completed retraction theorem was found. All four old proof dependencies remain
   used, no realized unit step is bypassed, and no DAG node is pruned.
5. The node's proof, proof_deps, and proof_origin already describe exactly this
   argument and its four reused leaves; they need no change. No new node fields or
   declaration records are necessary.

Changed only imports and documentation after reading: removed the redundant
quotient-operations import, made Henselian a plain proof import, documented the
proved standard-etale helper's source and argument, and recorded the import
interface repair and downstream review. The mathematical proofs were left intact.
