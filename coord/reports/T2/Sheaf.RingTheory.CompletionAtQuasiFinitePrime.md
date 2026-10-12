## What changed

Repair of reviewer X-dca65 point B2: the finite-subalgebra split node now defines
ι as the composite localization/completion map, defines f, Ip and Iq, and states
the quotient-coordinate hypothesis explicitly with the requested wording. This
matches the existing Lean signature; no Lean declaration or proof changed.

`Sheaf.RingTheory.CompletionAtQuasiFinitePrime` keeps its existing theorem signature and
public imports byte for byte. Its proof first calls
`Algebra.exists_finite_subalgebra_away_of_isQuasiFiniteAtPrime`, installs the returned
`Module.Finite` instance, constructs the compatible completed local map, and applies the
finite-subalgebra decomposition theorem. Only proof imports and the proof body changed.

`Sheaf.RingTheory.CompletionAtQuasiFinitePrimeMap` now proves
`Algebra.exists_completion_map_atPrime` directly from Mathlib's ideal quotient maps and
`AdicCompletion.liftRingHom`. Its statement needs neither quasi-finiteness nor finiteness
nor Noetherianity. It introduces no definition or chosen data from an unproved theorem.

`Sheaf.RingTheory.CompletionAtQuasiFinitePrimeSplit` replaces the first worker's false
unconditional splitting statement with `Algebra.completion_split_of_finite_subalgebra_away`.
It takes an explicit finite R-subalgebra S', an element outside q, a bijective canonical
away map, and a compatible completion map as inputs. Its remaining proof is exactly the
finite-subalgebra portion of Stacks 07NC (original steps 2–8), with a complete proof in
its docstring. The proof dependency imports are private; signature imports are public.
The item's DAG proof, proof_deps and proof_origin now record this actual reduction.

## Proved and sorry left

Original hole closed: `Algebra.completion_at_quasiFiniteAtPrime` (node
`lem-weil-pbc-completion-at-quasi-finite-prime`), with a proof reducing to the already stated
finite-subalgebra theorem and one new, strictly smaller remaining theorem.

New auxiliary theorem proved without sorry: `Algebra.exists_completion_map_atPrime`
(node `lem-weil-pbc-completion-local-map-at-prime`). This closes the first worker's proposed
map hole, replacing `Algebra.exists_completion_map_at_quasiFiniteAtPrime` with a more
general proved statement.

New hole added and the only sorry in the delivered files:
`Algebra.completion_split_of_finite_subalgebra_away`
(node `lem-weil-pbc-completion-finite-subalgebra-away-split`). The first worker's false
`Algebra.completion_split_of_compatible_map` is removed entirely, not left as an axiom.

Against the repository baseline this is a decomposition: 1 original hole closed, 1 new
hole added, net 0 in the target import closure. The existing finite-subalgebra-away
statement remains imported and is not claimed proved by this delivery. The main theorem
still depends on sorryAx through open dependencies; it is not an axiom-free completion
of the mathematical result. The proved map depends only on propext, Classical.choice
and Quot.sound. Explicit scratch-copy #print axioms checks found only these three and,
for the main and remaining splitting theorem, sorryAx.

## No longer needed

The item's direct proof import `Sheaf.RingTheory.CompletionFiniteExtension` is removed;
it is retained as a proof dependency import of the new finite-subalgebra helper, where
its decomposition is needed. No module is removed from the import closure. The unused private Mathlib import
`Mathlib.RingTheory.Localization.BaseChange` was also removed from the new split module;
the tensor-localization step remains recorded in its DAG plan.

The old direct proof_deps edges to `def-weil-pbc-module-localization-away`,
`def-weil-pbc-localization-at-prime`, `def-weil-pbc-adic-completion`,
`lem-weil-pbc-completion-finite-extension`, `def-weil-finitely-generated-module`, and
`lem-weil-pbc-localization-tensor-over-base` move to the new helper nodes. These six nodes
remain transitively needed. The finite-subalgebra-away and quasi-finiteness definition
edges stay direct. No original dependency node is globally pruned; pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

The first worker's `completion_split_of_compatible_map` omitted the quasi-finiteness
assumption entirely. For R = a field k, S = k[t], q = (t), its hypotheses hold, and the
unique compatible map on completions is the canonical inclusion k → k[[t]]. The required pure-tensor
projection would then be the polynomial inclusion k[t] → k[[t]], which is not surjective,
whereas a projection of a product ring equivalence must be surjective. Thus the original
split-off theorem was false (STATEMENT-DISPUTED: missing the quasi-finite/finite-subalgebra
condition). Its docstring lacked a proof, and both proposed nodes merely copied old
searches and had placeholder signatures. The existing item's DAG was also not updated.
All these faults are repaired in this delivery. No statement already in the repository
is changed, and no change record or forced adaptation is needed.

The unavailable LeanSearch service is recorded as unavailable, not as a no-match search.
LeanFinder, Loogle and source grep ran through msearch.py. The original eight-step Stacks
route remains; length alone is not a reason to abandon or replace a unit route.

## New nodes

`lem-weil-pbc-completion-local-map-at-prime` states just the levelwise compatible map for
prime localizations, proved by ideal-power quotient maps and the inverse-limit universal
property. It is the natural-map portion of 07NC, not its splitting conclusion. Searches
found Mathlib's liftRingHom and evaluation lemmas, which the proof uses; no duplicate
specialized declaration was found in the project or the upstream source.

`lem-weil-pbc-completion-finite-subalgebra-away-split` states the remaining direct-factor
argument once the finite-subalgebra/away-isomorphism data and compatible completion map
have already been supplied. It has no quasi-finite hypothesis and does not prove or
restate the construction of those data: that is performed in the main module from the
existing node. It follows steps 2–8 of 07NC, including the natural-projection check.
Searches found tensor localization tools but no theorem already stating this splitting.
Both nodes have self-contained statements, their actual Lean signatures, fresh recorded
searches, proof steps with the correct union of uses, source, provenance and creation data.
No change records were added.

## Earlier second reading (a previous round; superseded)

1. **Interfaces:** diffed the only existing module against the repository. The theorem's
   signature is byte-for-byte identical, with unchanged public imports and docstring;
   only its proof and private proof imports change. The other two modules and their
   corrected declarations are new and not previously visible. Verdict: pass.
2. **Proof and axioms:** all three files compile locally in import order through
   lcompile.py without errors or warnings. The sole delivered sorry is the named,
   source-documented finite-subalgebra helper. No axiom, unsafe, opaque, implemented_by,
   extern or holed definition occurs. Scratch copies with #print axioms show the standard
   three axioms for the map, plus only sorryAx for the remaining helper and main theorem.
   Verdict: pass as a documented decomposition, not an axiom-free proof of the item.
3. **Split-off statements:** rejected the false original helper by the k[t] counterexample.
   The replacement takes the precise finite-subalgebra data of the plan and has the full
   denominator, completion and idempotent proof in its docstring and node. Tested its
   boundary cases in words: g = 1 forces S' = S and reduces to the finite-extension
   decomposition; a nilpotent g cannot lie outside a prime; a zero S has no prime; at
   n = 0 both quotient-coordinate assertions are trivial. The map construction works
   without Noetherianity. Fresh semantic/type/source searches and rg in both library roots
   and upstream found supporting tools but no duplicate helper. Verdict: pass.
4. **Top-down reduction and pruning:** the main proof now actually uses the existing
   finite-subalgebra-away declaration, rather than handing off the whole quasi-finite
   theorem to a renamed hole. The map hole was closed from Mathlib. Removed the unused
   direct finite-extension import and retained that dependency in the remaining helper's
   planned proof. All old dependency nodes remain transitively needed. Checked
   dag/units/sk-thm-p1.json realized: no realized statement or step is bypassed or changed;
   the original finite-subalgebra → finite-extension → localization/idempotent route
   stays within this node. Verdict: pass; no globally pruned modules.
5. **DAG agreement:** repaired the item's missing proof update; checked each new node's
   statement against its Lean declaration and each proof_deps against the union of uses.
   The new map node records the proved Mathlib construction; the remaining helper records
   the finite-extension and tensor-localization steps it still needs. Verdict: pass.

Changes by this second reading: proved and generalized the completion-map helper; removed
the false decomposition statement and replaced it with the true finite-subalgebra
remaining argument; made the main proof call its existing finite-subalgebra dependency;
repaired docstrings, imports, node identifiers, signatures, dependency records, searches,
and the report. No existing mathematical interface was altered.


## Earlier second reading (a previous round; superseded)

1. Compared the existing module with the repository using diff. Its existing declaration,
   full signature, public imports and docstring are byte for byte unchanged; only private
   proof imports and its proof differ. The two auxiliary modules are new. No existing
   definition or statement changes, hence no change record is required. Verdict: pass.
2. Compiled all three delivered modules in import order with lcompile.py, then compiled
   scratch copies with #print axioms for all three theorems. The map uses exactly propext,
   Classical.choice and Quot.sound; the main theorem and split helper also use sorryAx.
   The only textual hole is the named split theorem with its source and proof docstring.
   No forbidden declaration or hollow definition occurs. Verdict: pass as a decomposition.
3. Read the remaining split statement against Stacks 07NC and the finite-extension theorem
   it uses. The finite subalgebra and bijective away map replace only the first step of
   the original argument; they do not repackage the whole target under another name.
   Tested g = 1 (finite-algebra case), nilpotent g (excluded by hg), zero S (no prime),
   and n = 0 (zero quotient). For arbitrary supplied ψ, quotient representatives and
   equality of all coordinates determine it uniquely; this supplies the R-compatibility
   required by the tensor map. Fresh LeanFinder, Loogle and msearch grep queries, together
   with rg on both project roots and upstream RingTheory, found supporting tools but no
   duplicate splitting result. The remaining idempotent and localization proof is not
   a few-minute closure. Verdict: true, needed and strictly smaller; one split-off hole.
4. The main proof actually extracts finite-subalgebra data from the existing dependency,
   constructs the completion map by the proved helper, and combines these to apply the
   split helper. The map proof uses Mathlib directly. All six removed direct DAG edges
   are accounted for in No longer needed and remain transitively needed. Inspected the
   realized fields of dag/units/sk-thm-p1.json: no realized node or unit step is bypassed.
   Removed the unused private Mathlib BaseChange import; kept the finite-extension
   dependency for the documented remaining route. Verdict: pass; globally pruned: none.
5. Compared the existing node diff: only proof, proof_deps and proof_origin change.
   Checked both new signatures against Lean, required metadata, source and proof
   docstrings, and proof_deps against the union of step uses. Corrected the map node's
   provenance text, which incorrectly referred to the finite-subalgebra portion.
   Verdict: pass.

Changes in this reading: removed the unused private BaseChange import, made the split
helper's surjectivity calculation explicit (including both denominator exponents),
corrected the completion-map provenance text, and recorded fresh independent checks.
No mathematical interface changed. One original hole is closed and one new hole added,
so this delivery is a net-zero decomposition, with an independently proved map helper.

## Second reading by T2

1. Interfaces: read and diffed the existing module against the repository. Checked the
   declaration signature byte for byte and the list of public imports separately; both
   are unchanged. Its diff contains only private imports and the proof body. The other
   two modules are new. The existing node changes only proof, proof_deps and proof_origin.
   No existing statement or definition changes; no change record is needed. Verdict: pass.
2. Proof: compiled all three modules with lcompile.py in import order. Independently
   compiled scratch copies with #print axioms for each declaration: the completion-map
   helper uses propext, Classical.choice and Quot.sound; the main theorem and splitting
   helper additionally use sorryAx. Scanned the delivered Lean files: exactly one sorry,
   in the named splitting theorem; no forbidden declaration or definition occurs. The
   main proof extracts real finite-subalgebra data from its existing dependency and uses
   the proved map helper. It defines no data by choosing an arbitrary unproved witness.
   Verdict: valid decomposition, one original hole closed and one new hole added, net 0;
   the main theorem is not yet axiom-free.
3. Split-off statement: read Stacks 07NC at https://stacks.math.columbia.edu/tag/07NC,
   since the cited literature/algebra.tex is absent on this machine. Matched the finite
   subalgebra, Module.Finite, g outside q and bijective canonical away map with the
   source's inputs after its initial construction. Read completion_finite_extension:
   its S'-algebra equivalence and completed-base coordinate formula give exactly the
   factor and map compatibility used here. The supplied psi is unique because every
   quotient class has a representative and completion coordinates determine elements;
   its hypothesis is not a weaker substitute for the natural map. Checked g = 1 (the
   finite-algebra case), nilpotent g (excluded by hg), zero S (no prime), n = 0 (zero
   quotient), and k = l = 0 in the denominator calculation. The remaining helper is true,
   needed, and strictly smaller than the item: construction of S' and g is already done
   by the main proof. Fresh msearch LeanFinder query on idempotent summands under away
   localization found IsLocalization.away_of_isIdempotentElem and
   AlgEquiv.prodQuotientOfIsIdempotentElem; these support steps, not the whole theorem.
   A Loogle query AdicCompletion, RingHom found liftRingHom and evaluation lemmas, already
   used. A grep query on idempotents/localization/completion and rg on both project roots
   and upstream RingTheory found no duplicate splitting result. No few-minute closure
   of the remaining local-isomorphism, tensor and factor argument was found. Verdict: pass.
4. Route and pruning: the main proof uses the recorded finite-subalgebra declaration,
   constructs psi by Mathlib, then applies the smaller remaining splitting statement.
   Read sk-thm-p1.json realized: this replaces no realized unit statement or step. All
   six former direct proof dependencies are listed under No longer needed and remain
   dependencies of the new helpers. Localization-tensor-over-base is a Mathlib leaf
   (IsLocalizedModule.rTensor and map_lTensor), not a missing Sheaf declaration. The
   finite-extension proof import stays private in the split helper; existing public
   imports stay unchanged, and new public imports supply signature notions. Verdict:
   pass; no globally pruned module and no replacement of the unit route.
5. Nodes: opened all three delivered JSON nodes. Checked both new Lean signatures
   verbatim against their lean.statement fields, required source/creation/blueprint
   metadata, and the equality of proof_deps with the union of each proof's uses.
   The finite-subalgebra node now explicitly defines f, Ip, Iq and the composite iota,
   and states the exact quantified coordinate implication of its Lean signature; this
   repairs the reported B2 objection. The map node describes the actual proved quotient
   construction, and the item node describes its three calls and final packaging.
   Verdict: pass.

Changes in this reading: added the missing module-level source/blueprint docstrings to
both new auxiliary modules. No theorem signature, proof body, dependency or mathematical
statement changed. Retained the accurate net-zero decomposition accounting above.
