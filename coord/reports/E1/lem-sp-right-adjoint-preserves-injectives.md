# lem-sp-right-adjoint-preserves-injectives

## Worker result

Files written: dag/nodes/sec-picard-framework/lem-sp-right-adjoint-preserves-injectives.json and this report. No new nodes.

The item is a Mathlib leaf. Its statement is the implication (b) to (c) of Stacks Homology, Lemma Tag 015Z, label lemma-adjoint-preserve-injectives (homology.tex:7270): the source assumes additive functors between abelian categories; an exact functor is additive and preserves monomorphisms. In pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, CategoryTheory.Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (Mathlib/CategoryTheory/Preadditive/Injective/Preserves.lean:49) gives the conclusion, with Functor.preservesMonomorphisms_of_map_exact (Mathlib/CategoryTheory/Abelian/Exact.lean:251) supplying its only extra input. The Hom-extension argument in the blueprint is exactly the proof of Stacks 015Z. The original statement and its two definition dependencies are unchanged.

Blueprint search: blueprint_refs.py search right adjoint injective, search functor injective, and search adjunction across all chapters found no second blueprint node stating this general categorical lemma; the other injective-preservation nodes are special sheaf applications. The blueprint.same_as result is [].

No Lean declaration is attached under B10. The sorry-free slopmaster2 theorem CategoryTheory.Adjunction.preservesInjectiveObjects_of_preservesFiniteLimits (WeilConjectures/Mathlib/CategoryTheory/Preadditive/Injective/Preserves.lean:35) assumes preservation of finite limits, which is stronger than the imported item's exactness hypothesis and is itself proved by the generic Mathlib criterion; it is not an exact statement match. The pinned Mathlib theorem is the appropriate leaf.

No sorry, imports, or new nodes. Nothing was changed in the unit or chapter. blueprint_refs.py check and review_split.py pass. check_dag.py --cycles reports zero cycles and seven existing unreachable-node warnings outside this item.

## Review by E1

I read Homology Lemma 015Z (`lemma-adjoint-preserve-injectives`) and its proof in `homology.tex`. The item is precisely its implication from exact left adjoint to injective-preserving right adjoint, with the source and target categories oriented correctly. I opened `Mathlib/CategoryTheory/Preadditive/Injective/Preserves.lean:49-52` and `Mathlib/CategoryTheory/Abelian/Exact.lean:249-253`: the former gives preservation of injectives from an adjunction and preservation of monomorphisms; the latter supplies that preservation from exactness. These two declarations specialize directly to the item, so the Mathlib leaf is justified. There are no new nodes or proof steps to check under B/C/D; the removed imported prose is the same Hom extension calculation already in the cited Mathlib theorem. The whole-blueprint search found no duplicate statement. I checked the identity adjunction and a zero abelian category as small cases; no extra enough-injectives hypothesis is needed for this direction. No A-F issue was found or sent back.

