## Worker report

This is the resumed stage-2 assignment, confirmed by the launcher's message and the live queue entry (stage 2, state). The old stage-1 sandbox contains only an unchanged reviewed split and a disposition report; it is not a stage-2 delivery. The current packet preserves the accepted natural-language statement and split, and changes only the item's lean record. One new module is provided: lean/Sheaf/AlgebraicGeometry/FiniteGroupSchemePrimaryOrder.lean, declaring AlgebraicGeometry.finite_commutative_group_scheme_primary_order with a single sorry proof.

Hypothesis and clause correspondence:

- An algebraically closed field k is `{k : Type u} [Field k] [IsAlgClosed k]`; arbitrary u is retained. The node's group scheme is `(G : Over (Spec (.of k))) [GrpObj G]`, commutativity is `[IsCommMonObj G]`, and finiteness over k is `[IsFinite G.hom]`. These are exactly the existing def-sc-group-scheme representation, with no reducedness or etaleness assumption.
- A prime ell different from the characteristic is `(ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ ringChar k)`. Characteristic zero is included.
- N is written explicitly as G.hom.finrankΓ. The existing definition installs the algebra on global sections using G.hom, and takes the k-dimension. The first conjunct `1 ≤ G.hom.finrankΓ` records positivity, with no positivity hypothesis.
- G(k) is the type `𝟙_ (Over (Spec (.of k))) ⟶ G`, namely morphisms from the terminal k-scheme. `Finite` of this type is the second conjunct. It is a conclusion, never an assumed instance.
- The primary subgroup is Mathlib's `CommGroup.primaryComponent` of this morphism group. Its membership theorem, read in Mathlib/GroupTheory/Torsion.lean:459, is exactly existence of a natural a with x^(ell^a)=1. The morphism group is written multiplicatively, so this is precisely ell^a x=0 in the node. `Nat.card` of the subgroup is asserted equal to `ℓ ^ padicValNat ℓ G.hom.finrankΓ` in the third conjunct.
- On positive natural N, Mathlib's padicValNat is the exponent of ell in N: PadicVal/Defs.lean gives padicValNat_def and PadicVal/Basic.lean defines the integer valuation by padicValNat of the absolute value. This is the integer valuation in the node, used at positive N; no new valuation is introduced.
- The last conjunct quantifies over every natural n with `max 1 (padicValNat ℓ G.hom.finrankΓ) ≤ n` and gives the cardinality of the subtype of all rational points with `x ^ (ℓ ^ n) = 1`. The node's integer n is necessarily at least one, so natural n covers exactly its range. No let binders or hidden structures are used.

Dependencies and sources read: def-weil-field uses Mathlib Field; def-weil-algebraic-closure records IsAlgClosed in Mathlib.FieldTheory.IsAlgClosed.Basic (class at line 62, polynomial splitting, equivalent to the root formulation). def-sc-group-scheme records GrpObj and the existing conventions explicitly explained in WeilConjectures.AlgebraicGeometry.GroupScheme.Defs; I read its header, GrpObj-based conventions, and Scheme.Hom.finrankΓ in WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree:96-101. def-weil-l-adic-numbers supplies the valuation convention; the statement uses its integer specialization padicValNat rather than requiring an irrelevant completion. All required definitions are public imports.

Proof imports: WeilConjectures.AlgebraicGeometry.GroupScheme.Finite supplies the connected-order, prime-to-characteristic etaleness, and finite-etale-points statements; its public dependencies also supply Mathlib's field-flatness lemma. Mathlib.GroupTheory.Sylow supplies Sylow.card_eq_multiplicity, and Mathlib.GroupTheory.OrderOfElement supplies the finite-group cardinal-annihilator theorem. The local-constant-product proof prerequisite has no Lean record yet, so its import is deferred; no new declaration for that proof-only prerequisite is needed to state this item. The declaration docstring reproduces all five accepted proof steps, including the characteristic-zero use of positive N and the case e=0. I read Milne Algebraic Groups printed p.210 (PDF page 222) and pp.220-221 (PDF pages 232-233), verifying Proposition 11.3 and Corollaries 11.30-11.31.

Edge cases: the trivial group scheme has N=1 and e=0, so both cardinalities are one. In characteristic p, alpha_p and mu_p have a single k-point and scheme order p, so for ell different from p the formula again gives one. An etale constant ell-group gives its full primary cardinality and stabilizes by n=e. Products of local p-primary and etale factors retain scheme multiplicities in N while discarding only the p-factor in the ell-valuation. The empty scheme is excluded by a group scheme's unit, not by an added nonemptiness assumption. The threshold n=max(1,e), characteristic zero, and arbitrary field universe are all retained.

Searches actually run with msearch.py, preserved in searches.jsonl:

- leanfinder: "A finite commutative group scheme over an algebraically closed field has ell primary rational points of cardinality ell to the valuation of its scheme theoretic order for ell different from the characteristic". Eight finite-field hits; none compares scheme order and rational points.
- loogle: `"primaryComponent"`. Twelve hits; CommGroup.primaryComponent and its membership theorem give the already existing subgroup notion, but no group-scheme cardinality theorem.
- grep: `primaryComponent|card_points_eq_finrank|primary.*order`, subdirectory AlgebraicGeometry. Zero Mathlib hits.
- leansearch: "For a finite commutative group scheme over an algebraically closed field the ell primary subgroup of rational points has order ell raised to the ell adic valuation of its scheme theoretic order". Eight primary-component hits, providing the subgroup definition but no geometric order comparison.

I also searched WeilConjectures and Sheaf by the exact blueprint id and by primary-order, finite-group primary/torsion, primary/finrank and padicValNat/finrankΓ patterns. No declaration states the entire node; the finite-etale point-count theorem covers only the etale case, and the scheme-order-annihilator module states a different fact. No new notion, duplicate definition, statement correction or dependency repair is needed.

The first compiler check found that tensor-unit notation required opening CategoryTheory.MonoidalCategory. I added that namespace opening; the statement itself did not change. Validation uses only the prescribed scompile.py and deliver2.py wrappers.

## Review by Q79

I compared the complete node with the complete signature: all four conclusions are present, finiteness is a conclusion, the characteristic condition is inequality of natural characteristic and ell, the point group is the existing Hom group in Over, and the order remains the global-section dimension. I checked the primaryComponent membership definition and the valuation specialization rather than introducing copies. I also checked that the stabilization subtype ranges over all k-points and that n has exactly the stated lower bound. Only one named theorem is postponed, with the accepted five-step proof in its docstring. This is my self-check; no independent second worker was started, under the direct-delivery brief.

## Second reading by Q79

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
