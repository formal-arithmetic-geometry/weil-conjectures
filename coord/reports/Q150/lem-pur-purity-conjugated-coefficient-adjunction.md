## Worker report

The module `Sheaf.CategoryTheory.PurityConjugatedCoefficientAdjunction` states
`CategoryTheory.purity_conjugated_coefficient_adjunction`, with its sole proof `sorry`.
It contains no new definitions, auxiliary theorems, or instances. The node changes only
in `lean`; its recorded signature is verbatim from the module. No statement correction,
new node, dependency repair, or STATEMENT-DISPUTED flag is needed.

I read the complete item, its two statement dependencies and their Mathlib matches,
their declarations and docstrings, and the proof dependency. I also read the current
blueprint's `sk-lem-sp-field-extension/_section.md` and sole proof paragraph under
`literature/blueprint/latest/`, and Stacks `categories.tex`, Tag 0037, including the
unit/counit discussion. The blueprint asks for coefficient-extension comparisons carrying
units and counits and respecting composition; the item isolates the categorical
conjugation calculation used to obtain those comparisons from purity.

Hypotheses, matched individually:

- The preordered set is `{I : Type w} [Preorder I]`. Neither nonemptiness nor linearity
  nor antisymmetry is assumed.
- The categories are `X : I → Type uX` and `Y : I → Type uY` with the two dependent
  `Category` instance binders. Their object and morphism universes and the index universe
  are independently explicit.
- The functors are `P`, `J`, and `H`. The specified adjunction is `adjJ i : P i ⊣ J i`;
  its `unit` and `counit` are exactly the specified eta-J and epsilon-J. Purity is the
  arbitrary family `γ i : H i ≅ J i`.
- The coefficient functors are `CX i j hij` and `CY i j hij` for `hij : i ≤ j`.
  The argument order `(i,j)` encodes the subscript `ji` in the TeX.
- The left comparison is `b i j hij : P i ⋙ CY i j hij ≅ CX i j hij ⋙ P j`.
  The right comparison is `c i j hij : J i ⋙ CX i j hij ≅ CY i j hij ⋙ J j`.
  Lean's functor composition and morphism composition run in diagrammatic order, so
  these types are exactly the stated right-to-left mathematical compositions.
- `hunit` is the displayed J-unit identity, beginning with `CX.map (adjJ.unit.app M)`,
  followed by `c.hom.app (P.obj M)` and `J.map (b.hom.app M)`.
- `hcounit` is the displayed J-counit identity, beginning with `b.hom.app (J.obj K)`,
  followed by `P.map (c.hom.app K)` and `adjJ.counit.app (CY.obj K)`.

Conclusions, matched clause by clause in the order of the conjunction:

1. The witnesses `adjH : ∀ i, P i ⊣ H i` and the first two conjuncts assert that the
   given formulas really are the unit and counit of an adjunction. In particular the
   triangle identities and naturality are part of the Mathlib `Adjunction` structure.
   They give `adjH.unit = adjJ.unit ≫ γ.inv` componentwise and
   `adjH.counit = P.map γ.hom ≫ adjJ.counit` componentwise.
2. The witness `a i j hij : H i ⋙ CX i j hij ≅ CY i j hij ⋙ H j` is a natural
   isomorphism, not just a family of maps. The third conjunct fixes every hom component
   to `CX.map γ.hom ≫ c.hom ≫ γ.inv`, exactly the displayed formula. Thus `a` is
   determined by the canonical formula; it is not an arbitrary comparison.
3. The fourth conjunct is the H-unit square with the same `b` parameter.
4. The fifth conjunct is the H-counit square with the same `b` parameter.
5. The sixth conjunct universally quantifies the two families of specified natural
   associators `αX` and `αY`, each from the composite coefficient functor to the direct
   coefficient functor. Under precisely the displayed `c` cocycle, its conclusion is
   the displayed `a` cocycle with those same associators. The direct transition uses
   `le_trans hij hjk`; all other proofs of that relation give the same transition by
   proof irrelevance. No pentagon or additional coherence hypothesis is imposed.
6. The seventh conjunct quantifies each index and arbitrary specified coefficient
   unitors `uX : CX i i (le_refl i) ≅ 𝟭 (X i)` and the analogous `uY`.
   The two premises express exactly that `b_ii` and `c_ii` are identities under those
   unitors. Explicitly, they are `uY.hom ≫ P.map uX.inv` and
   `uX.hom ≫ J.map uY.inv`, respectively. The conclusion is
   `a_ii = uX.hom ≫ H.map uY.inv`. This retains nontrivial coefficient unitors.
7. The original `b`, the coefficient functors, associators and unitors are retained,
   rather than replaced by new witnesses. Consequently any originally supplied `b`
   cocycle is literally unchanged. The module docstring records this structural
   conclusion; no tautological `b`-cocycle-implies-itself conjunct is added.
8. The only conditions on `γ` are its individual natural-isomorphism types. There is
   no relation between different indices, no faithfulness of coefficient functors,
   and no reduction or conservativity hypothesis.

Dependency declarations used:

- `def-nagata-category`: `CategoryTheory.Category` in
  `Mathlib.CategoryTheory.Category.Basic` (read the full class and `CategoryStruct`).
- `def-weil-pbc-adjunction-mate`: the Mathlib match is `CategoryTheory.mateEquiv` in
  `Mathlib.CategoryTheory.Adjunction.Mates`. That public import supplies the recorded
  adjunction/unit/counit interface and ordinary functors and natural isomorphisms.
  This lemma does not need to introduce or use a different mate construction.
- Proof dependency `lem-weil-pbc-adjunction-of-natural-bijection`:
  `CategoryTheory.Adjunction.mkOfHomEquiv` in `Mathlib.CategoryTheory.Adjunction.Basic`,
  imported explicitly for the proof plan. Its `CoreHomEquiv` signature and constructor
  were read in full. The declaration's six proof-plan steps reproduce every step of
  the node, including the inverse cancellation and the nontrivial unitor formula.

Edge cases checked before writing: an empty index type leaves the existential families
empty and all clauses vacuous, without a nonemptiness hypothesis; empty categories do
not cause an illicit choice of objects; identity functors and identity purity maps
recover the original comparisons; nontrivial unitors are explicitly retained; no
faithfulness is required for cancellation of actual isomorphisms. The formulas type in
independent object and hom universes. Associator and identity conclusions are conditional,
so the theorem does not assume that a coefficient system comes with these data when
only the two adjunction squares are being used.

Searches for an existing statement (2026-10-24):

- `msearch.py ... leanfinder "Transport adjunctions across right adjoint natural
  isomorphisms preserving coefficient comparison squares cocycles and unitors"`:
  eight hits, including `Adjunction.ofNatIsoRight`, `natIsoOfRightAdjointNatIso`,
  `rightAdjointUniq_trans_app`, and `conjugateIsoEquiv`. None states the simultaneous
  two comparison squares, arbitrary coefficient associators and identity unitors.
- `msearch.py ... loogle "CategoryTheory.Adjunction.ofNatIsoRight"`: five hits,
  the transport constructor and its unit, counit and Hom-equivalence formulas.
  These give the single-adjunction transport, not the full node.
- `msearch.py ... leansearch "Transport an adjunction through a natural isomorphism
  of right adjoints preserving comparison unit counit squares and composition cocycle"`:
  eight hits, including the same transport and uniqueness APIs. No full match.
- `msearch.py ... grep "ofNatIsoRight|conjugate.*cocycle" CategoryTheory`: thirteen
  hits, ordinary adjunction transports and their usages; no matching cocycle statement.
- Project `rg` searches in `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json` for the item id and
  `purity_conjugated_coefficient_adjunction|conjugatedCoefficientAdjunction|
  conjugated_coefficient_adjunction` found no declaration. Broader
  `conjugated.*coefficient|coefficient.*conjugat` found specialized coefficient-change
  statements. I read `CoeffCompatible.of_conj` in upstream
  `SixFunctors/Etale/Derived/CoefficientChangeExchange.lean`; it states only one
  coefficient-compatibility square for a conjugation and is not this result.
- Mathlib and both project source roots were also searched for the proposed full
  declaration name, with no collision. No private copy of any existing notion is used.

Validation: `scompile.py Q150 lem-pur-purity-conjugated-coefficient-adjunction` on the
delivered module compiled both its sandbox view and library-name view successfully
(2.4 s and 6.0 s). No errors or unexpected warnings. All Lean lines are at most
100 characters. `autoImplicit` is disabled; every universe and variable is explicit.

## Second reading by Q150

This is the worker's final consistency check; the maintainer supplies the independent
delivery review. I reread the node next to the complete module and checked the direction
of every arrow, in particular the J- and H-counit squares and the inverse unitor in each
identity-normalized comparison. Each displayed formula appears with its factors reversed
only to accommodate Lean's diagrammatic composition. The existential witnesses carry
actual adjunction and natural-isomorphism structures, with their components fixed by
the stated formulas. The associators and unitors are quantified conditionally, and no
new compatibility of `γ`, pentagon, faithful functor, or nonempty index premise appears.
No mismatch was found and no node-text change was made.
