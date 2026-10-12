## What changed
Proved `existsUnique_open_of_etale_subsheaf_final` by constructing the unique witness from
two strict intermediate obligations: existence of a support open and its stalk criterion.
Proved uniqueness directly by testing the factorization property on both open immersions.
The two remaining obligations each occupy a separate new module, with full proof sketches.
The target signature and its original docstring are unchanged.

## Proved and sorry left
Proved `AlgebraicGeometry.Scheme.existsUnique_open_of_etale_subsheaf_final` and the private
helper `unique_open_etale_subsheaf_final_factorization`.
Sorry remains only in `AlgebraicGeometry.Scheme.exists_open_etale_subsheaf_final_factorization`
(node `lem-weil-pbc-etale-subsheaf-final-open-parts-factorization`) and
`AlgebraicGeometry.Scheme.etale_subsheaf_final_stalk_criterion`
(node `lem-weil-pbc-etale-subsheaf-final-open-parts-stalk`).

## No longer needed
The previous attempt's uniqueness obligation and its proposed node/module are unnecessary:
uniqueness is proved directly using Mathlib's étale open immersions and their underlying maps.
No original imports were removed. In the new support-open module the unnecessarily broad
`Mathlib.AlgebraicGeometry.Sites.EtalePoint` import was replaced by
`Mathlib.AlgebraicGeometry.Sites.Etale`; the stalk module imports `EtalePoint` explicitly. The original node's dependencies remain needed transitively
for the support and stalk obligations; none of those mathematical dependencies is pruned.

## Where the brief, the DAG or earlier work was wrong
The earlier attempt kept its new sorries inside the target module, so the delivery checker
still classified the target as containing sorry. Moving the two genuine component obligations
into imported modules fixes that issue. Its uniqueness sorry was unnecessary. Its new node
records lacked complete proof sketches, full Lean signatures, and actual search evidence;
these are replaced. LeanSearch is unavailable (HTTP internal server error); the logged Loogle
and grep searches ran successfully. Empty schemes and empty opens cause no uniqueness issue:
the proof uses inclusions without any nonemptiness assumption.

## New nodes
`lem-weil-pbc-etale-subsheaf-final-open-parts-factorization` records construction and gluing
of the support open in `Sheaf.AlgebraicGeometry.EtaleSubsheafSupportOpen`.
`lem-weil-pbc-etale-subsheaf-final-open-parts-stalk` records the pointed-neighbourhood and
filtered-colimit argument in `Sheaf.AlgebraicGeometry.EtaleSubsheafSupportStalk`.
No existing statement or definition changes; no change record is required.


## Second reading by J2
1. Compared the delivered target module against the repository with `diff -u`: its only
   existing declaration has its entire signature and original docstring byte for byte
   unchanged. The two support modules and the private uniqueness helper are new. The
   factorization definition expands literally to the target's section-property conjunct;
   it contains no postponed data or proof. No existing definition changes or change records.
   Verdict: pass.
2. Compiled all three delivered modules locally with `lcompile.py --all`, without errors
   or warnings. Searched their source for prohibited declarations and postponements: the
   only two sorries are exactly the two public named obligations listed above. Compiled a
   scratch copy with `#print axioms` for the target, both obligations and the private helper.
   Uniqueness uses only `propext`, `Classical.choice`, `Quot.sound`; the target and the two
   open obligations additionally use `sorryAx`, exactly as expected. The target is a proved
   reduction, not an axiom-free completion. Verdict: pass with the two advertised obligations.
3. Read both new statements, their docstrings and nodes. Existence omits uniqueness and
   the stalk assertions; the stalk criterion assumes a specified open's section property,
   rather than asserting existence. Neither restates the whole item. Checked empty S,
   empty U, W bottom and W top: empty coverings give a unique section on the empty object;
   there are no geometric points of empty S; stalks outside the support are empty. The
   sheaf gluing and pointed-neighbourhood proofs require no extra hypotheses. Independent
   LeanFinder, Loogle and grep searches with subterminal/support/fiber terminology found
   site, subterminal, mono-preservation and colimit machinery, but no existing theorem
   proving either obligation. Also searched both repository roots and read Mathlib's point
   fiber API (joint surjectivity and filteredness). Closing either remaining obligation
   requires substantial formal gluing or geometric-fiber infrastructure; no short direct
   application was found. Verdict: true, properly smaller obligations with complete proofs
   in words and matching nodes.
4. The proof uses the two components and proves uniqueness by the two inclusions obtained
   from testing W and W' themselves. Checked the four old proof dependencies: sheaf of sets,
   openness of etale maps, geometric stalks and geometric points remain used in the two
   component arguments. None is pruned. The added target import is proof-only; public
   imports in the new modules provide names occurring in their signatures. Replaced the
   support-open module's overly broad EtalePoint import by Etale and put EtalePoint in the
   stalk module. Read `dag/units/sk-thm-iff.json`: neither this item nor its split obligations
   bypasses a realized unit statement/step; the Tag 04HV route is retained. Verdict: pass.
5. Compared the target node diff and all new node records with the Lean. The target's
   three steps describe choosing the support, adding its stalk criterion and proving
   uniqueness. Its proof_deps are exactly the two new obligations; their dependency unions
   and document proof origins agree with their docstrings. New nodes have source, searches,
   split status, created/blueprint/chapter/unit and Lean records. Replaced flattened new
   Lean signatures by the verbatim multiline signatures and appended the independent
   search evidence. Verdict: pass.

Changed only the placement/scope of imports in the two new modules, verbatim new-node
Lean signature records, search evidence, and this report; the reviewed proofs were retained.
