# Q82 stage-1 delivery

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-sheaf-rees-symmetric-presentation.json`: item, statement; six-step split, no direct Mathlib match.
- `citations.json`: sixteen step/node entries, each checked as a literal substring of the current cited statement.
- No new nodes, no new Mathlib leaves, no unit-file changes. The item is not a unit key node.

## Attachments

None. I searched the live `lean/WeilConjectures/` by the blueprint tag and by Rees/symmetric terminology. `AlgebraicGeometry.Scheme.IdealSheafData.reesData` in `AlgebraicGeometry/RelativeProj/Rees.lean` gives affine-basis Rees data but does not state the sheaf symmetric-algebra morphism or its homogeneous surjectivity. Its surrounding coefficientwise base-change and multiplication declarations likewise do not cover every clause. Thus they cannot justify ATTACH for this item.

## WANTED

None: all source passages used are in the read repository.

## Problems found and corrected

The imported statement is correct and remains unchanged. Its proof was empty. The subtlety is that the Rees algebra is a coproduct of module sheaves; arbitrary sections do not commute with arbitrary coproducts. Step 1 computes its affine sections using the existing restriction-colimit and affine associated-sheaf statements, rather than assuming a sectionwise definition. No global quasi-separatedness, finite generation of the ideal, or Noetherian hypothesis is inserted.

While checking the tag table I corrected my draft's tag for `divisors-lemma-blowing-up-affine` to **0804**. Tag **02NS**, `lemma-blowing-up-projective`, is the item's source for the displayed symmetric-to-Rees surjection; its projectivity conclusion requires finite type, but that conclusion is not used here. The surjection itself does not require finite type, as the monomial proof establishes.

The inherited `blueprint.from.node` is null (the ancestor command reports this); its detailed `from.place` and `via` chain are retained, since these are maintainer-owned provenance. Whole-blueprint searches for `Rees`, `Rees algebra`, and `symmetric algebra` found no blueprint node stating this entire sheaf-level assertion. The related `lem-sfb-blowup-rees-symmetric-presentation` cites the present item and adds the blowup/relative-Proj comparison; using it here would be circular.

## Not duplicates

No new nodes were created. The ring Rees definition, ideal-power definition, affine tilde adjunction, restriction-colimit lemma, symmetric algebra sheaf theorem, symmetric grading theorem, and canonical symmetric graded algebra were reused directly. Hence no same-tag new/existing pair needs justification.

## Review by Q82

I read the item and its chapter/unit records, the current blueprint provenance, and the local Stacks passages: Divisors 02NS (`lemma-blowing-up-projective`) and 0804 (`lemma-blowing-up-affine`); Schemes 01HV (`lemma-spec-sheaves`), 01I7 (`lemma-compare-constructions`), 01IA (`lemma-quasi-coherent-affine`), 01IB (`lemma-equivalence-quasi-coherent`), 01ID (`lemma-colimit-quasi-coherent`); Modules 01AJ (`lemma-exactness-pushforward-pullback`), 01BG (`lemma-pullback-quasi-coherent`), 01CF (`section-symmetric-exterior`), 01CG (`lemma-local-tensor-algebra`), and 01CL (`lemma-whole-tensor-algebra-permanence`); Algebra 00DM (`section-tensor-algebra`). There are no new nodes whose sources need a separate audit. The complete proof is an agent-written expansion of these source constructions, so its origin is marked agent.

For Step 1 I opened `def-sbc-ideal-sheaf-powers`, which explicitly gives the affine associated sheaves and their powers; `def-nagata-sheaf-rees-algebra`, which explicitly constructs the coproduct; `lem-weil-pbc-module-restriction-open-immersion-colimits`, whose clause (1) preserves this coproduct upon passage to an affine open; and `lem-weil-pbc-affine-tilde-gamma-adjunction`, whose clauses (4) and (2) identify the restricted coproduct with the associated sheaf of the module direct sum and then recover its sections. The diagram is discrete on the small set of natural numbers. The required open immersion is the inclusion of the chosen affine open, and the coefficient modules are exactly the powers specified by the ideal-power node. No section functor is assumed to preserve a coproduct.

For Step 2 I checked the statements of the Rees ring and sheaf definitions: the former says precisely that the degree-n coefficient belongs to I^n, and the latter specifies multiplication on summands and the degree-zero unit. Finite-tuple summation and coefficient extraction are inverse, preserve products by the displayed homogeneous multiplication, and give identity on scalars. This is an elementary calculation from those constructions, not a missing ring-theory comparison lemma.

For Step 3 I reread the ideal-power presentation, the sheaf Rees inclusions, and `lem-weil-pbc-spec-module-tilde-sections`. The latter explicitly states the principal-open localization map and its restriction compatibility. An arbitrary affine restriction is computed via the maps of the ideal subsheaves, not by pretending it is itself a single localization. Its polynomial formula is coefficientwise restriction; the principal-open specialization is a/1. No intersection of two affine opens is assumed affine.

For Step 4 I reread both clauses of `lem-weil-pbc-quasi-coherent-symmetric-algebra`. Clause (a) is the actual universal property for arbitrary commutative algebra sheaves, not merely full faithfulness or a definition of symmetric algebra; clause (b) supplies the affine sections identification. Its hypotheses hold because I is quasi-coherent and the existing Rees definition gives a commutative O_X-algebra and a linear degree-one insertion. The universal property proves uniqueness among all algebra-sheaf maps extending that insertion. Multiplicativity supplies the precise monomial formula and fixes scalars.

For Step 5 I checked `lem-weil-pbc-symmetric-algebra-graded`: its statement explicitly says the homogeneous piece is spanned by products of n generators, with degree zero R. `def-trf-canonical-symmetric-graded-algebra` specifies precisely this grading on affine sections. Thus the monomial formula really implies degree preservation. For surjectivity the proof spells out induction on n using the definition of the product ideal: finite sums of products in I^n I give finite R-linear combinations of products of n+1 elements of I. The source of a preimage is explicitly a finite sum of symmetric monomials of the same degree. This argument is a few-line induction, not an additional independent theorem moved into a new node.

For Step 6 the canonical symmetric algebra's statement gives exactly the scalar/generator restriction formula used, and the symmetric grading statement gives the monomial spanning used to extend the equality. Both routes send a scalar times a monomial to the displayed restricted product times t^n. This checks the actual compatibility equation, rather than asserting that transport is automatic. It is also the naturality of the already constructed sheaf map. I declared the generic off-unit tools in `split_report.tool_uses`: these are algebra/sheaf prerequisites of the existing blowup route, not a replacement route for alteration or finite-coefficient purity.

I checked delivery-errors B through E against the actual JSON and source statements. No new node disguises an elementary calculation, duplicates another node, or restates one of the item's clauses. Every non-elementary input is an existing cited node, and every citation quote is copied from its statement. The proofs use no SGA source, no Lean was written or compiled, and the read repository was not modified. All six proof steps have fewer than 900 characters; none hides a long comparison argument. The small cases are: n=0 (identity on R, with the empty product 1); I=0 (all positive target pieces zero); I=R (Rees algebra R[t]); a nilpotent or square-zero ideal (the corresponding higher target pieces vanish); and the empty affine/zero ring (all section modules zero). In particular surjectivity does not assert injectivity of the symmetric-to-Rees map. No nonzero-ring, nonempty-scheme, finite-type, or Noetherian assumption enters.

Mathlib searches were run through the required command and logged in `searches.jsonl`; I preserved the item's earlier Q56 searches and appended only Q82's actual searches. I read the returned Rees and symmetric-algebra sources. `reesAlgebra`, `mem_reesAlgebra_iff`, and `adjoin_monomial_eq_reesAlgebra` concern a ring ideal, while `SymmetricAlgebra.lift` concerns a module over a ring. They do not give the complete sheaf assertion by a one-line specialization. The second semantic phrasing likewise returned ring coefficient/ideal-sheaf-data statements, not this theorem.

## Unfinished work

None in the requested one-level split. All required arguments are in the item, and no additional statement-only nodes are needed. Delivery is subject to the server dry run below.
