1. Files written:

- `lem-pc-zero-scheme-pullback-local-coefficient.json`: item, split into one proof step.
- `lem-pc-zero-scheme-pullback-full-local-coefficient.json`: one new statement node, attached to the closed declaration `AlgebraicGeometry.Scheme.Modules.IsFreeGenerator.exists_pullback`; Mathlib verdict: no match.
- `citations.json`: one verbatim statement quote for the proof step.

2. Attachments:

- `AlgebraicGeometry.Scheme.Modules.IsFreeGenerator.exists_pullback` belongs to `lem-pc-zero-scheme-pullback-full-local-coefficient`.

3. WANTED: none.

4. The item is a restriction of the source theorem from the full inverse-image open to an arbitrary affine open `V`; it is not itself an exact declaration attachment. I searched the DAG and blueprint for the full inverse-image coefficient statement and found no existing node. The source declaration at `ZeroLocus.lean:391-396` has the same hypotheses and conclusion as the new node. The item-level searches found only general Mathlib pullback/free-module APIs, not this scheme-local statement; LeanSearch was unavailable and is recorded as such.

## Review by E1

I read `WeilConjectures/AlgebraicGeometry/Modules/ZeroLocus.lean`, lines 388-446, including the complete proof of `IsFreeGenerator.exists_pullback`. The new node copies its mathematical statement: a morphism of sheaves of modules with free generators on `W` pulls back to free generators on `g^{-1}(W)` with coefficient `g.app W b`; its source and hypotheses were checked against lines 391-396, and the declaration has no `sorry`. The item adds the hypothesis that `U` and `V` are affine and `V ⊆ g^{-1}(U)` and asks for the restricted generators.

Step 1 uses exactly the new node's conclusion. Restricting a free generator along an open inclusion preserves the defining bijection because restriction maps compose; restricting the coefficient equation gives `g.appLE U V b` by functoriality of the structure-sheaf maps. This is the only elementary argument after the cited theorem. I checked the identity morphism, zero coefficient, unit coefficient over an affine field, and the empty scheme: restriction yields the expected generators and the same coefficient formula. The citation quote is copied verbatim from the new node statement.

The full-inverse-image statement was searched with LeanFinder, Loogle, grep, and LeanSearch through `msearch.py`; LeanFinder returned only generic Mathlib pullback APIs, Loogle and grep returned no match, and LeanSearch was unavailable. The item was searched with the same four tools and the same verdicts. No duplicate node or blueprint statement was found. The new node is statement-only and records the sorry-free slopmaster2 declaration as closed.

## Second reading by E1

- Item statement: checked against `ZeroLocus.lean`, `IsFreeGenerator.exists_pullback`, lines 388-446; the affine hypotheses, containment `V \subseteq g^{-1}(U)`, pulled-back free generators, and `g.appLE U V b` coefficient all agree.
- New node `lem-pc-zero-scheme-pullback-full-local-coefficient`: checked against the declaration statement at lines 391-396; its schemes, module sheaves, free-generator hypotheses, pullback modules, and coefficient conclusion agree, and the attached declaration is sorry-free.
- Step 1: checked against the cited full pullback statement; applying it at `W=U`, then restricting sections along `V \subseteq g^{-1}(U)`, gives the displayed coefficient by restriction functoriality. The restriction argument is elementary from the definitions and section-map composition.
- Edge cases: identity morphism, zero coefficient, unit coefficient over a field, and empty scheme all preserve the stated generator and coefficient conclusions; affine opens and the `n=0,1` cases introduce no additional hypotheses.
- Existing-node and blueprint searches: searched the DAG and blueprint for the full inverse-image pullback/free-generator fact and for the item statement; no duplicate or blueprint statement was found. Mathlib searches and their actual verdicts are recorded in `searches.jsonl`.

No files required mathematical repair in the second reading; this section records the independent statement, dependency, source, and edge-case checks before delivery.
