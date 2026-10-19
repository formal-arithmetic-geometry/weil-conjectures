## Worker report

Files written:

- `dag/nodes/sec-proetale-coefficients/lem-sfb-modobj-kernels.json`: statement, split into five elementary arguments; no Mathlib match.
- `citations.json`: a verbatim extract of each cited statement for every step that cites it.
- `report.md`: this report. `searches.jsonl` is the search command's own log.

New nodes: none. New Mathlib leaves: none.

Attachments: none. Searches of the slopmaster2 project under `WeilConjectures/` and `Comparator/` for the blueprint id, `CategoryTheory.Mod.isLimitKernelFork`, module objects and kernel terminology gave no matching declaration. The upstream master file `WeilConjectures/CategoryTheory/ModuleObjects/Abelian.lean:47–105` implements the same construction (`kernelSMul`, `kernelObj`, `kernelι`, `isLimitKernelFork`), but that checkout is reference material only and was not used to claim completion.

WANTED: none. The proof follows the available blueprint, marked `proof_origin.by = agent` as required for an agent-written source.

The imported statement is correct and has been preserved verbatim. Its proof had no cited definitions, `elementary: null`, and suppressed the action-law calculations. I expanded the cancellations and both action laws, justified zero morphisms in the module category, and cited the existing definitions of preadditivity and additive functors for the only zero-map argument. No kernel preservation by tensor, flatness, abelian hypothesis, symmetry, commutativity of the monoid, or existence of any other limits is needed.

Metadata issue reported for maintenance: this main-20261015 imported node has no `chapter`, `unit`, or `lean_audit` fields. There is no `dag/chapters/sec-proetale-coefficients.json` or `dag/units/sk-prop-sfb-module-category.json` to read. I read their current blueprint `_section.md` files and the unit's proof instead, and retained all maintainer-owned metadata unchanged. This is not a request for a new proof route: the five steps realize the kernel assertion of Part 1 in the specified unit. The item is not its unit's key statement, so no unit realization record is delivered.

Nothing mathematical remains unfinished at this one-level split. A fresh second reader must review and deliver; I have not pushed it.

## Not duplicates

No new nodes were created. The whole-DAG searches and `tools/blueprint_refs.py search` for `kernel`, `Kernels of module objects`, `kernel fork`, `module objects`, and `additive functor` found the existing module-object definitions and the neighboring cokernel and exactness nodes. The cokernel node requires right exactness and asserts a different universal property. The unit's combined abelian-structure statement assumes the ambient category abelian and tensor right exact; it is not the same statement as this kernel result under the weaker hypotheses. No other blueprint node states this entire result with the same hypotheses. `blueprint.same_as` is therefore empty; `from` remains null because the item itself is a blueprint node.

## Mathlib searches

All nine entries in `mathlib_searches` are the exact tool/query pairs actually run by `msearch.py`, with actual hit counts and top results retained from `searches.jsonl`. Both semantic services and Loogle responded successfully. I tried two semantic phrasings with each service before concluding that the item is absent.

I read `Mathlib/CategoryTheory/Monoidal/Mod.lean` in full: it defines internal modules and their forgetful and restriction-of-scalars functors but no kernel lift. I also opened `Monoidal/Internal/Limits.lean`, `Monoidal/Internal/Module.lean`, `CategoryTheory/Action/Limits.lean`, and `Algebra/Category/ModuleCat/Kernels.lean`. Limits in `Mon C` concern variable monoid objects; `Action V G` concerns external monoids acting by endomorphisms; `ModuleCat.kernelIsLimit` and `ModuleCat.isLimitKernelFork` concern concrete modules over an ordinary ring. None specializes in one line to arbitrary internal modules. The search whose scope was a single file made the wrapper misparse line numbers as file names (25, 40, 59, 68, 71); this output is recorded faithfully and was followed by reading the file and another directory-wide grep, not treated as evidence of absence by itself.

## Review by Q31

I read the statement and two-paragraph proof in `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-prop-sfb-module-category/lem-sfb-modobj-kernels.md` and its companion `.proof.md`, the containing unit `_section.md` and proof, and the chapter `_section.md`. The statement agrees clause by clause: arbitrary preadditive monoidal category, tensor additive in both variables, arbitrary monoid object, arbitrary module morphism with just its underlying kernel, unique compatible action, and the kernel universal property in internal modules. There is no `blueprint_update` field to supersede the source. I also read the current statements of `sk-def-sfb-module-objects`, `def-weil-preadditive-category` and `def-weil-pbc-additive-functor`, and Stacks Tag 00ZY (`homology.tex`, label `definition-preadditive`) for the latter two notions. No new node needs a separate source.

Step 1 unpacks the assumed kernel universal property and proves monicity by uniqueness of a lift. It cites nothing because both statements are established directly from that hypothesis. The argument works with an arbitrary domain T and does not assume all kernels or a zero object.

Step 2 uses exactly the bilinearity stated by `def-weil-preadditive-category`, the Hom-group-homomorphism condition stated by `def-weil-pbc-additive-functor`, and the module-map equation stated in part 2 of `sk-def-sfb-module-objects`. Bilinearity gives zero compositions by cancellation, and additivity gives tensoring the zero morphism equal to the zero morphism. Here zero is a morphism, not a zero object: the blueprint shorthand R tensor 0 has this meaning. These facts establish both that the module category has zero morphisms and that the candidate action is killed by f. The underlying kernel property then supplies the unique action map. This is a direct application of a hypothesis, not an uncited existence theorem.

Step 3 uses the unit axiom for M from part 1 of the module definition. Naturality of the left unitor and of tensoring with eta are part of the monoidal-category structure. The displayed chain has domain 1 tensor K and codomain M, so cancellation by iota proves the unit equation without cancelling a tensor of iota.

Step 4 uses the associativity axiom for M from that same definition. I checked every associator's domain: both sides start at (R tensor R) tensor K. Naturality of mu moves the inclusion across multiplication, and naturality of alpha moves it across the associator. Functoriality and the defining equation of gamma_K give the last two equalities. Only iota is cancelled; R tensor iota is never asserted monic. Thus no tensor exactness hypothesis is silently used. The defining action equation is then literally the module-map condition for the inclusion.

Step 5 uses part 2 and the category description of `sk-def-sfb-module-objects`: g is linear, and equality and composition are inherited from the ambient category. The displayed equation proves linearity of the unique underlying kernel lift h. Uniqueness follows from uniqueness in the assumed ambient kernel. The zero morphism assertion already checked in step 2 identifies f iota = 0 in the module category. Both existence and uniqueness clauses of the categorical kernel are therefore present.

For C1/C4 I copied each quoted portion directly from these three node statements into `citations.json`. No step takes an assertion from a cited node's proof. All five steps are elementary under the brief's few-line rule: they are the explicit kernel universal property and equations from definitions, with the slightly longer associativity chain written in full. There is no hidden non-elementary exactness, limit-lifting, or coherence theorem; only functoriality and the given natural transformations' naturality occur. Creating a node for these equations would manufacture elementary facts or restate the item's own clauses, violating B/D.

For small cases I checked f = 0 with iota = id_M (the action is gamma_M and every linear g factors as itself), f = id_M in any example where its kernel exists (the construction restricts to that kernel), R the tensor unit (the action equation is the left unitor and the construction recovers the original kernel), and concrete abelian groups with tensor product and a nonflat internal ring. The latter still works because the proof never tensors a kernel as a limit. No nonzero-object, nonzero-ring, characteristic, or size condition enters. Noncommutative monoids are allowed because no factors of R are interchanged.

I corrected the missing justifications and citations, not the statement. Against delivery-errors B–E: there are no new nodes, no duplicate or restated clause, no Mathlib leaf asserted without a matching theorem, no invented search, no changed blueprint fields/import flags, no tag used as a substitute for an argument, no off-unit theorem replacing the unit route, and no circular use of the abelian or exact-forgetful results that depend on this item. The three cited dependencies define only the notions used. Every source actually used is available locally and no SGA source is used.

## Second reading by Q31

- Item statement: checked against the imported blueprint node and its source text; all hypotheses and the kernel-in-module conclusion agree, with no missing or extra assumptions.
- Step 1: checked against the kernel universal property in the item statement; the monomorphism cancellation argument is valid for an arbitrary test object and uses no extra limits.
- Step 2: checked against `def-weil-preadditive-category`, `def-weil-pbc-additive-functor`, and `sk-def-sfb-module-objects`; bilinearity and additivity justify zero compositions and the descended action equation exactly under the stated hypotheses.
- Step 3: checked against the unit axiom in `sk-def-sfb-module-objects` and unitor/tensor naturality; the displayed composites have matching domains and cancellation uses only the kernel inclusion.
- Step 4: checked against the associativity axiom in `sk-def-sfb-module-objects`; every associator and tensor composite is well typed, and no tensor preservation of monomorphisms or kernels is assumed.
- Step 5: checked against the module-map equation and the underlying kernel universal property; the lift is linear, unique, and gives the categorical kernel in the module category.
- New nodes: none; there were no new statements to audit, source-check, deduplicate, or search for Mathlib matches.

Small cases independently checked: for the zero map with kernel inclusion the identity the construction recovers the given action; for an identity map with zero kernel its unique action and unique module lift satisfy the equations; over a field it restricts a representation to its ordinary invariant kernel. The displayed proof also works in the zero category and for a noncommutative monoid object, since it never interchanges tensor factors.

I also opened Stacks `homology.tex`, label `definition-preadditive` (Tag 00ZY): it states precisely the two Hom-group definitions used here. An independent `msearch.py` leanfinder query, "Internal modules over a monoid object have equalizers created by the forgetful functor in a preadditive monoidal category", returned eight concrete-module limit results, including `ModuleCat.forget_reflectsLimits`, `ModuleCat.forget_preservesLimits`, and `FGModuleCat.forget₂CreatesLimit`; none has the arbitrary internal-module statement. The actual result is in `searches.jsonl`. A fresh source search of slopmaster2 for the item id, `isLimitKernelFork`, and `kernelSMul` found no declaration stating the item.

Changes made in this second reading: added this independent audit and its actual search log only; no mathematical or citation repair was needed. The worker's expanded proof and metadata are retained.

Verification: the delivery tool's dry run printed `OK (not pushed) deliver/Q31/lem-sfb-modobj-kernels at df895d2b78: preflight passed`. The installed tool accepts the two positional arguments shown in its help; the brief's trailing `.` is rejected as an extra argument, so the successful invocation omitted it.
