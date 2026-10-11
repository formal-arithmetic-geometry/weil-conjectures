## Worker report

The module `Sheaf.CategoryTheory.EssentiallyConstantSplitting` states
`CategoryTheory.Functor.essentiallyConstant_splitting`, with its sole proof `sorry`.
No definitions, dependency modules, new nodes or statement corrections are needed.

Hypotheses and objects, matched individually:

- The inverse system of abelian groups is `F : ℕᵒᵖ ⥤ AddCommGrpCat.{u}`.
  As in the recorded dependency, index `n` represents the positive integer `n+1`;
  thus `i₀ : ℕ` includes every positive starting index and all inequalities are preserved.
  The composite `t(k,j)` is `F.map (homOfLE hjk).op`; identity and composition
  are supplied by the functor laws, rather than extra assumptions.
- The value is `X : AddCommGrpCat.{u}`; the cone homomorphisms are `π`.
  `hπ` is precisely adjacent transition compatibility.
- `i₀` and `r` are the splitting index and homomorphism supplied by essential constancy.
  `hr : π i₀ ≫ r = 𝟙 X` renders (a).
- `hfactor` renders (b) for every index `j`, with witnesses `k`, `hik : i₀ ≤ k`
  and `hjk : j ≤ k`, equivalent to `k ≥ max(i₀,j)`.
  Categorical composition reverses the displayed functional-composition order,
  so its equality is exactly `t(k,j) = π j ∘ r ∘ t(k,i₀)`.
  These binders are the explicit witnesses of the existing dependency definition
  `CategoryTheory.Functor.IsEssentiallyConstantWithValue F X`, whose full body
  was read. Its existential proposition is deliberately unpacked because the
  node supplies these PARTICULAR witnesses, rather than asking for some splitting.
  This adds no hypothesis or private definition of essential constancy.
- The local `p j hj` is `F.map (homOfLE hj).op ≫ r` and `Z j hj` is
  `(p j hj).hom.ker`, Mathlib's additive subgroup kernel.

Conclusions, matched clause by clause:

1. The first conjunct says `π j ≫ p j hj = 𝟙 X`, then
   `Function.Injective (π j)`. For each `c`, it asserts a unique pair
   `a : X × Z j hj` with `c = π j a.1 + ↑a.2` and `a.1 = p j hj c`.
   This is exactly the node's stated internal direct sum and explicit coordinate formula.
   Specifying the formula inside the unique-existence predicate does not weaken uniqueness:
   any pair decomposing `c` has that coordinate by the preceding retraction equality.
2. The second conjunct quantifies all `k ≥ j ≥ i₀`. It gives both transition
   identities, followed by membership of the image of every `z : Z k` in `Z j`.
   Its last equality explicitly says the transition respects the two decompositions.
   The restricted maps are additive homomorphisms because the original maps are;
   the kernel subgroups are closed under addition. Membership lets those maps
   restrict to the subgroups. Their identity and composition laws are inherited
   from `F`, since restriction preserves the underlying function. Thus these
   kernels with the specified restricted transition maps form the inverse system
   stated in clause (2), with no extra choice or separate notion required.
3. The third conjunct provides `k ≥ j` for each `j ≥ i₀`, and says every
   element of `Z k` maps to zero. This is exactly `t(k,j)(Z k) = 0`.

Dependencies used:

- `def-weil-inverse-system`: Mathlib module
  `Mathlib.CategoryTheory.Functor.OfSequence`, declarations
  `CategoryTheory.Functor.ofOpSequence` and `CategoryTheory.NatTrans.ofOpSequence`.
  Read their full signatures and constructor docstrings; the recorded equivalent
  functor formulation is used. This import is provided transitively by the next module.
- `def-weil-pbc-essentially-constant-system`: imported module
  `Sheaf.CategoryTheory.EssentiallyConstantSystem`, declarations
  `CategoryTheory.Functor.IsEssentiallyConstantWithValue` and
  `CategoryTheory.Functor.IsEssentiallyConstant`. Their witnesses, including adjacent
  cone compatibility and both inequalities, are exactly the theorem's explicit data.
- `Mathlib.Algebra.Group.Subgroup.Ker` supplies `AddMonoidHom.ker`, used for `Z`.

Edge cases checked before writing: `j=i₀`, `k=j`, and the first positive index
(represented by zero) are included. For a constant tower and identity retraction,
`Z=0` and `k=j` works. For a tower with zero adjacent maps, the cone value can
be zero, `Z=C`, and `k=j+1` gives vanishing, so no eventual-isomorphism condition
has slipped in. The zero value and zero terms are allowed. No finite generation,
finiteness, nontriviality or characteristic condition is imposed. The universe
`u` is explicit and arbitrary, following the existing dependency's universe.

Source read: [Stacks Tag 070C](https://stacks.math.columbia.edu/tag/070C), forward
implication and its kernel construction. The local literature checkout does not
contain `homology.tex`, so the primary source was opened online. The node already
explains use of the supplied cone value in place of the limit; no limit assumption
is needed for this elementary forward splitting. No node fault or dispute found.
The declaration docstring carries all four proof steps from the node.

Searches (all via `msearch.py C1 lem-weil-pbc-essentially-constant-splitting` unless stated):

- LeanFinder: `essentially constant inverse system decomposes as constant value and
  essentially zero kernels`: 8 hits, chiefly unrelated probability kernels and
  `InverseSystem.piSplitLE` / `piSplitLE_eq` (products of lower intervals), no match.
- Loogle: `IsEssentiallyConstant, AddMonoidHom.ker`: zero hits, unknown identifier
  `IsEssentiallyConstant`.
- Mathlib grep: `EssentiallyConstant|essentially.constant|ker_isCompl_range` in
  `CategoryTheory`: zero hits.
- LeanSearch: `essentially constant inverse system splitting into value and kernels`:
  service unavailable, Internal Server Error; no absence verdict inferred from it.
- Direct `rg` for `EssentiallyConstant|essentially.constant|` followed by the item id
  in the source project's `WeilConjectures` and project's `lean/Sheaf`: only the
  already recorded essential-constancy definition and an unrelated derived-category
  comment; no existing theorem for the item. The item-id search has no source hit.
- Direct `rg` for `essentiallyConstant_splitting|essentiallyConstantSplitting` in
  `dag/lean_names_upstream.json`, Mathlib, source and project Lean: no collision.

Validation: server `scompile.py` compiled the module cleanly in 1.1 seconds,
without warnings or errors. The delivery dry run is run as the final worker check;
the independent second reading is left to the next worker, as instructed.

## Second reading by C1

I independently opened the item node, both statement-dependency nodes, the full
`EssentiallyConstantSystem.lean` definitions, Mathlib's `Functor.ofOpSequence`
and `NatTrans.ofOpSequence` signatures/docstrings, and the delivered module.
No statement mismatch was found; the module and node record are unchanged.
Only this independent review section was added.

Source check: the local Stacks checkout is absent. I read the primary-source
pages [070C](https://stacks.math.columbia.edu/tag/070C),
[05PU](https://stacks.math.columbia.edu/tag/05PU), and
[05PV](https://stacks.math.columbia.edu/tag/05PV), and fetched/read the relevant
labelled passages of `homology.tex` and `categories.tex` from the Stacks project's
GitHub master source. 070C assumes an abelian category and uses the limit value;
the node explicitly specializes to abelian groups and uses the supplied cone
value of 05PU(2). The forward kernel argument uses only these cone maps and the
retraction/factorization data, so no additional limit hypothesis is required.
The cofiltered hypothesis of 05PU(2) holds for the fixed nonempty natural-number
tower. No finiteness, Noetherian, coefficient-field, or characteristic assumption
occurs in these source passages.

Objects, hypotheses, and conclusions of the node, matched item by item:

1. Objects `C_i`, abelian groups, indexed by positive integers: rendered by
   `F : ℕᵒᵖ ⥤ AddCommGrpCat.{u}`, with `C_(n+1) = F.obj (op n)`.
   Verdict: exact, using the equivalent functor presentation in
   `def-weil-inverse-system`, not a replacement notion.
2. Composite transitions `t_(k,j)`, with identity and composition laws:
   `F.map (homOfLE hjk).op`; the functor supplies both laws. Verdict: exact.
   I checked Mathlib's opposite-sequence constructor examples as well as its type.
3. Value `X` and homomorphisms `π_i`: `X : AddCommGrpCat.{u}` and
   `π : ∀ n : ℕ, X ⟶ F.obj (op n)`. Verdict: exact.
4. Adjacent cone compatibility: `hπ` asserts
   `π (n + 1) ≫ F.map (homOfLE (Nat.le_add_right n 1)).op = π n`.
   Verdict: exactly the node's adjacent compatibility, not an extra naturality
   hypothesis; compatibility for composites follows by iteration.
5. Supplied index and retraction: `i₀ : ℕ`,
   `r : F.obj (op i₀) ⟶ X`, `hr : π i₀ ≫ r = 𝟙 X`.
   Verdict: exact, including the first positive starting index.
6. Essential-constancy factorization for every index: `hfactor` quantifies
   `∀ j : ℕ`, then `∃ k`, `hik : i₀ ≤ k`, `hjk : j ≤ k`, and equates
   the transition with `F.map (homOfLE hik).op ≫ r ≫ π j`.
   Verdict: exactly `k ≥ max(i₀,j)` and the functional composite in (b).
   These are the particular witnesses in the dependency definition
   `IsEssentiallyConstantWithValue`; unpacking its existential data preserves
   the node's supplied witnesses and introduces no new Prop definition.
7. Tail projection and kernel: local `p j hj = F.map (homOfLE hj).op ≫ r`
   and `Z j hj = (p j hj).hom.ker`. Verdict: exact, real data using Mathlib's
   additive subgroup kernel. The dependence on `hj` changes nothing by proof
   irrelevance. There are no hollow definitions.
8. Conclusion (1), retraction and injection for every tail index: first conjunct
   `∀ j hj, π j ≫ p j hj = 𝟙 X ∧ Function.Injective (π j) ∧ ...`.
   Verdict: exact with the same quantifier order.
9. Conclusion (1), internal direct sum and coordinate formula: for every `c`,
   `∃! a : X × Z j hj, c = π j a.1 + ↑a.2 ∧ a.1 = p j hj c`.
   Verdict: equivalent to the node's unique decomposition. Although the formula
   is inside the unique-existence predicate, every decomposing pair satisfies
   it: apply the preceding retraction identity to the decomposition, and use
   kernel membership. Thus uniqueness here is not weaker than the node's.
10. Conclusion (2), both transition identities for all `k ≥ j ≥ i₀`:
    the second conjunct quantifies `j k hj hjk` and asserts
    `F.map (...) ≫ p j hj = p k (hj.trans hjk)` and
    `π k ≫ F.map (...) = π j`. Verdict: exact; their order is immaterial.
11. Conclusion (2), restriction and inverse-system/decomposition compatibility:
    `∀ z : Z k ..., F.map (...) ↑z ∈ Z j hj`, followed by the equality
    sending `π k x + ↑z` to `π j x + F.map (...) ↑z`.
    Verdict: exact. The restricted homomorphism is uniquely determined by this
    underlying map; additivity and identity/composition follow from the original
    homomorphisms/functor, so the stated membership expresses the full restricted
    system without extra choices or an omitted hypothesis.
12. Conclusion (3), eventually zero kernels: the third conjunct is
    `∀ j hj, ∃ k hjk, ∀ z : Z k (hj.trans hjk), F.map (...) ↑z = 0`.
    Verdict: exactly a single later index for all elements, not an index
    depending on the element, and equivalent to zero image of the kernel.

Edge cases: `i₀ = 0` represents positive index 1, not an extra mathematical
index; `j = i₀` and `k = j` are included. All groups, including `X` and every
term, may be zero. Constant identity towers give zero kernels; a tower of
nonzero groups with zero adjacent transitions and value zero allows `k = j+1`,
confirming that eventual isomorphisms were not assumed. An empty index set is
outside this node, which fixes positive integers; schemes and dimensions are
not objects of this statement. No characteristic restriction exists. Universe
`u` is explicit and arbitrary, as in the dependency: the countably many groups
can all be placed in a common universe. Every variable is explicitly bound.

Independent searches, using words beyond the worker's queries:

- `msearch.py ... leanfinder "tower of abelian groups split retractions compatible
  kernels eventually zero transition maps"`: eight hits, principally
  `AddGroupExtension.Splitting.rightHom_splitting`,
  `CategoryTheory.ShortComplex.Splitting.s_r`, and related one-object splitting
  results. Their displayed signatures have no tower/eventual-zero conclusion;
  no existing declaration for this node.
- `msearch.py ... loogle '"essentiallyConstant"'`: successful, zero hits.
- `msearch.py ... leansearch "compatible split surjections from a tower of
  abelian groups give kernel tower with eventually vanishing maps"`: service
  Internal Server Error, recorded as unavailable, not evidence of absence.
- Direct `rg -n -i` for `essentially.?constant|essentially.?zero|split.*inverse|
  inverse.*split` on the source `WeilConjectures`, project `lean/Sheaf`, Mathlib
  `CategoryTheory`, and `Order/DirectedInverseSystem.lean`: the existing
  essential-constancy definition, unrelated comments, and
  `InjectiveTowerEmbedding.lean`. I opened the latter: it states embeddings
  into injective towers with split epimorphisms, not this kernel splitting.
  No matching system-level theorem exists in these results.

H5/H6/H8/H9 check: no new definitions or dependency modules are needed; the sole
proof is `sorry`. The declaration and module docstrings carry the source and
blueprint id. The proof docstring includes all four node steps (retraction,
unique kernel decomposition, transition compatibility, eventual vanishing),
with dependency ids where used. Both imports support the displayed statement;
namespace and file topic follow the project conventions. All lines are at most
100 characters. I checked programmatically that `lean.statement` is verbatim
identical to the signature before the theorem's `:= by`, and checked the
binders/universe by eye. There is no statement correction to audit and no new
or dependency node delivered.

Validation of the unchanged module: second reader's `scompile.py` compiled it
on the server in 1.0 seconds, exit code 0, no warnings or errors.
