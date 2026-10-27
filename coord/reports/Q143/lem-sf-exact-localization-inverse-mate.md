## Worker report

The module `Sheaf.SixFunctors.ExactLocalizationInverseMate` states
`CategoryTheory.exact_localization_inverse_mate`, with one `sorry` for the complete
statement of lem-sf-exact-localization-inverse-mate. No theorem is proved. The
source is Stacks 07A7, remark-base-change (sites-cohomology.tex, read at
4025–4075), together with the units/counits sentence of the current blueprint's
fix-prop-coherence.proof.md and the exact_hom_fac/exact_inverse_mate_isIso
calculations in SemilinearProperOpenMatePasting.lean, read at 1990–2110.

Hypothesis and clause correspondence:

- The four abelian categories are `{A : Type u₁}`, `{B : Type u₂}`,
  `{D : Type u₃}`, `{F : Type u₄}`, their explicit `Category` and `Abelian`
  instances. Twelve independent universe variables allow all object, ordinary
  morphism, and chosen derived morphism sizes.
- Chosen ordinary unbounded derived categories are the four
  `[HasDerivedCategory.{wᵢ} ...]` instances; the actual categories and
  localization are `DerivedCategory` and `DerivedCategory.Q`. No boundedness,
  resolutions, monoidal structures, or enough injectives are required.
- All six functors have the node's source and target, using Lean's left-to-right
  functor composition: `R₁ ⋙ G` represents GR₁, and `G ⋙ L₂` represents L₂G.
  Each has its `Additive`, `PreservesFiniteLimits`, and
  `PreservesFiniteColimits` instances, expressing additive exactness.
- The specified adjunctions are `(a₁ : L₁ ⊣ R₁)` and `(a₂ : L₂ ⊣ R₂)`;
  `(d : R₁ ⋙ G ≅ H ⋙ R₂)` is precisely the isomorphism in the given direction.
- β is `((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ d.hom)).natTrans`.
  Its assumed invertibility is the explicit `IsIso` instance on this term.
  No assumption equates the invertibility of d with that of its mate.
- The two derived adjunctions are the item-local universe-general helper
  `CategoryTheory.exactLocalizationDerivedAdjunction aᵢ`.
  Its definition localizes `aᵢ.mapHomologicalComplex (.up ℤ)` with the exact
  factorization isomorphisms, so the units and counits are the specified ones.
- D(d), including the exact-composition identifications, is
  `Functor.mapDerivedCategorySquareIso d` from the upstream module
  `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`.
- The first conclusion is `IsIso` of the inverse mate of this square for these
  derived adjunctions. The second is equality of that entire natural
  transformation with `(Functor.mapDerivedCategorySquareIso (asIso β)).hom`.
  `asIso` packages precisely β and its inverse from the assumed `IsIso`;
  this is the localization D(β), conjugated by the same standard composition
  isomorphisms. Thus the equality applies on all derived objects.
- The last two conjuncts give the requested Hom normalization, separately for
  a₁ and a₂, for every pair of unbounded cochain complexes K,L and every
  cochain map f. The left side is the localized adjunction's `homEquiv` on
  `Lᵢ.mapDerivedCategoryFactors.hom.app K ≫ Q.map f`. The right side is
  `Q.map ((aᵢ.mapHomologicalComplex (.up ℤ)).homEquiv _ _ f) ≫
  Rᵢ.mapDerivedCategoryFactors.inv.app L`. This has exactly the order of the
  node's right-to-left composition formula, translated to Lean's `≫`.
- There is no assumption of faithfulness of Q. The proof docstring explains
  extension of equality by `Localization.natTrans_ext` instead.

Dependency declarations read and used:

- def-weil-abstract-derived-category: `DerivedCategory`, `HasDerivedCategory`,
  and `DerivedCategory.Q` in `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- def-weil-exact-derived-adjunction: its live Q22 binding remains byte-identical,
  `SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction` in
  `Sheaf.SixFunctors.OpenTensorNormalizationData`, imported by the item.
  The item helper performs exactly the same localization with independent
  universes; it reduces to the recorded definition when the universes agree.
- def-weil-pbc-adjunction-mate: its mathlib_match is
  `CategoryTheory.mateEquiv`, `Mathlib.CategoryTheory.Adjunction.Mates`.
  The full forward and inverse definitions and their component descriptions
  were read. The statement uses `.symm` on d.hom, never d.inv.
- Proof leaf lem-weil-pbc-exact-functor-derived-factorization:
  `Functor.mapDerivedCategoryFactors`,
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`; imported publicly
  since the statement uses it.
- Proof leaf lem-weil-pbc-localization-universal-property:
  `Localization.lift`, `liftNatTrans`, `liftNatIso`, `natTrans_ext`,
  `Mathlib.CategoryTheory.Localization.Predicate`, available through the
  dependency's `Mathlib.CategoryTheory.Localization.Adjunction` import.
- Standard comparisons `Functor.mapDerivedCategoryCompIso` and
  `mapDerivedCategoryNatIso`, upstream
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.

Edge cases checked mathematically: zero abelian categories and zero complexes
make all formulas the unique maps. Identity functors and identity adjunctions
reduce to the original square. A nontrivial scalar automorphism of the identity
square retains its scalar, rather than its inverse, in the inverse mate; using
d.hom is essential. Arbitrary unbounded complexes and independent chosen
localization universes are admitted. Invertibility of β is a separate required
hypothesis and is not inferred from invertibility of d. No zero-category,
characteristic, nonemptiness, or degree restriction was introduced.

Searches made with the prescribed msearch.py wrapper (full receipts are in the
sandbox's searches.jsonl):

- LeanFinder: "Exact localization preserves the inverse mate of an exact
  adjunction square and normalizes its Hom adjunction bijection"; eight hits
  including mateEquiv, its forward/inverse component formulas, and mate pasting.
  None includes the specified localized adjunction and its Hom normalization.
- Loogle: "CategoryTheory.Adjunction.localization"; hits localization and
  localization_unit_app/localization_counit_app. These construct and describe
  the adjunction, without this mate/Hom statement.
- Mathlib grep: "mapDerivedCategorySquare|localization_unit_app|mapDerivedCategoryNatTrans"
  in CategoryTheory; one hit in Localization/Adjunction.lean.
- LeanSearch: "Localizing an exact adjunction preserves its inverse mate and
  Hom equivalence"; eight hits including localization and derived-adjunction
  construction/formulas, none stating this whole assertion.
- rg in project WeilConjectures and Sheaf for exact_hom_fac,
  exact_inverse_mate, exactLocalizationInverseMate, mapDerivedCategorySquareIso,
  exactDerivedAdjunction, and localization_inverse_mate. The two first matches
  are private helpers in SemilinearProperOpenMatePasting and do not expose the
  full equality. The upstream MapDerivedCategoryMate theorem uses a different
  derived adjunction and extra resolution/monoidal hypotheses, so is not the
  requested declaration. Its standard square-isomorphism definition is reused.
  The recorded exactDerivedAdjunction definition was inspected in full.
- Search for the item id in WeilConjectures and Sheaf found no declaration.
  No exact public duplicate of the complete statement was found.

The node's mathematical statement, dependencies, proof, and proof dependencies
are unchanged. No new notion or new DAG node is introduced. No unresolved
statement dispute or source fault was found.

## Returned H13 repair

The returned head f7d9d1fe3de2 incorrectly rebound the existing Q22 dependency
`def-weil-exact-derived-adjunction` to a new module. The initial saved-packet dry
run passed (374952aaca7), but the independent review's ownership finding still
requires repair. The dependency node copy and `ExactDerivedAdjunctionGeneral.lean`
have been removed from the packet. Thus the live dependency record, declaration,
and all existing users are untouched. No dependency-record repair is delivered.

Following the review's explicit alternative, the universe-general construction
is now the item-owned helper `CategoryTheory.exactLocalizationDerivedAdjunction`
in `ExactLocalizationInverseMate.lean`, listed in the item's lean.declarations.
Its docstring cites this item and Stacks 015F. It has exactly the same body as
the recorded definition: degreewise adjunction, CatCommSq isomorphisms given by
`mapDerivedCategoryFactors.symm`, and localization at quasi-isomorphisms.
There is no choice of an adjunction and no postponed proof in its data.
The helper allows six independent universes so the theorem retains twelve.
When all three pairs of universes agree, the helper and recorded definition
are definitionally equal; the sandbox normalization probe checks this by rfl.
This is a helper within the item, not a new owner or replacement of the existing
notion. The item theorem changes only the helper reference; its hypotheses and
four conclusion clauses remain as accepted by the independent review.

## Second reading by Q143

Reopened the node, the final item module, and the live dependency definition.
All four categories and six exact functors appear with their original directions. Checked that the assumption is
on `.symm` of mateEquiv, not its forward map; a first compile exposed an erroneous
forward-map term during drafting, which was replaced by the correct inverse mate.
The comparison on the right is `asIso` of precisely this inverse mate. The final
whole-natural-transformation equality therefore retains the original β rather
than replacing it with an inverse or an arbitrary isomorphism. The Hom formulas
quantify over the original two respective pairs of complexes and use the
specified localized adjunctions and correct hom/inv factorization directions.
Both conclusion clauses and both indexed Hom clauses are present, with no
faithfulness hypothesis. Removed drafting let binders from the statement.
Checked the item helper against the live recorded definition: its
factorizations and degreewise/localization operations are identical, while all
category and localization universes are independent. The six-step natural-language
proof in the theorem docstring follows the DAG proof and uses localization
uniqueness for all derived objects. Module and declaration docstrings cite their
own blueprint ids. No other node fields changed, and no theorem was proved.

## Validation of the repair

`scompile.py Q143 lem-sf-exact-localization-inverse-mate` compiled the item
module in both sandbox and library modes without errors or unexpected warnings
(2.5 s and 2.3 s). A second invocation compiled the item plus the module-mode
`scratchpad/NormalizationProbe.lean`; its `rfl` comparison of the helper with
the live Q22 declaration succeeded (2.9 s sandbox, 2.1 s library). The probe
is a self-check only and is not part of the delivered library. The only changed
DAG field is the item's `lean`; no dependency node is included.
