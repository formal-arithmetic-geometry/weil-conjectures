## Worker report

Item: lem-sfb-dg-compact-bimodule-full-faithfulness. The module
`Sheaf.CategoryTheory.DgCompactBimoduleFullFaithfulness` states
`CategoryTheory.DgAlgebra.derived_tensor_fully_faithful_of_compact_bimodule`.
Its only postponed proof is that theorem, with the node's five-step proof in its
docstring. No statement correction or disputed statement is needed.

Source read: `literature/stacks-project/dga.tex`,
`lemma-tensor-with-compact-fully-faithful` (Tag 09R9), including its proof and the
preceding tensor/Hom discussion and `lemma-tensor-hom-adjoint` (Tag 09LT).
The source's prose calls RHom a left adjoint in the proof, but its displayed Hom
bijection and unit, and this node, correctly use tensor as the left adjoint.

Hypothesis and clause correspondence:

- Size convention: explicit `universe u`; complexes have component modules in
  `ModuleCat.{u} (ULift.{u} ℤ)`. The existing `Derived` localization supplies the
  larger category and `DerivedStructure.coproducts` uses index universe u. This
  is the same convention as the recorded DG adjunction dependency. No site or
  additional size equality is imposed.
- Two associative unital integer DG algebras: `(A B : Algebra.{u})` uses the
  recorded `Mon Complex` definition. Its multiplication is a chain map, so it
  encodes both d² = 0 and the signed Leibniz rule. It imposes no commutativity.
- DG right modules and the actual unbounded derived categories: `RightModule A`,
  `RightModule B`, `Derived A`, and `Derived B` come from the dependency, with
  `[DerivedStructure A] [DerivedStructure B]` giving the standard shifts and
  distinguished mapping-cone triangles on those actual localizations.
- A DG (A,B)-bimodule: `(N : Bimod A B)` uses Mathlib's monoidal bimodule with
  its two actual chain-map actions, unit/associativity laws and commuting square.
- Forgetting only N's left action: the helper `bimoduleRightModule N` has
  `X := mop N.X` and `smul := N.actRight.mop`. Its law fields are direct images
  of N's supplied right-action laws. It has real data, with no choice or sorry.
  This is a canonical restriction helper within the notion already stated by
  the item, not a new independent mathematical definition.
- Use the specified derived tensor: `(F : RightModule A ⥤ RightModule B)` with
  `_tensor : BalancedTensorModel N F` specifies exactly balanced tensor, including
  its quotient, differential, naturality and induced right action. The binders
  `T`, `α : Q A ⋙ T ⟶ F ⋙ Q B`, and `[T.IsRightKanExtension α]` specify its total
  left derived functor by exactly the universal property used in
  `bimodule_derived_tensor_hom_adjunction`. Quantifying over models avoids making
  another choice of derived functor and includes every realization of T_N.
  These are specifications of the named functor, not additional hypotheses on N.
- Compactness: `hcompact : IsCompactObject.{u} ((Q B).obj (bimoduleRightModule N))`
  is the recorded upstream definition, with all coproducts in the fixed universe.
- Every integer degree: `hself : ∀ k : ℤ, ...` includes negative, zero and positive
  shifts. `S` and `e : ShiftComparison B k (bimoduleRightModule N) S` are an actual
  DG representative of N[k], with the unchanged right action and signed
  differential. They do not impose boundedness.
- Isomorphism of abelian groups: `φ : A.X.homology k ≃+ (N_D ⟶ N_D⟦k⟧)` is an
  additive equivalence, where N_D is the displayed localization of N. In the
  cochain convention `homology k` is H^k, with `homologyπ k` its cycle quotient.
- The isomorphism is specifically induced by the left action: for EVERY
  `z : A.X.cycles k`, the hypothesis requires a DG map `f : bimoduleRightModule N ⟶ S`.
  For all p and all n in N^p, the HEq states that f, read through the actual
  shifted-complex comparison, equals `N.actLeft` on the pure tensor
  `((A.X.iCycles k) z) ⊗ n`. Thus it is precisely n ↦ zn. HEq only reconciles
  degrees p+k and k+p. The following equation identifies `φ ((A.X.homologyπ k) z)`
  with `(Q B).map f` followed by the specified derived shift comparison.
  Surjectivity of the cycle quotient pins φ on every cohomology class. In
  particular boundaries have zero image. This is not a hypothesis of an
  arbitrary abstract additive equivalence with the right source and target.
- Full faithfulness means exactly the last clause:
  `∀ M P : Derived A, Function.Bijective (T.map : (M ⟶ P) → (T.obj M ⟶ T.obj P))`.
- No generation assumption occurs. There is no flatness, countability,
  boundedness, quasi-isomorphism between A and B, or commutativity binder.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.DgBimoduleDerivedAdjunction`,
  `CategoryTheory.DgAlgebra.bimodule_derived_tensor_hom_adjunction`: read its full
  signature/docstring; the statement uses the same tensor model, localization
  comparison, and right Kan extension property, without assuming its conclusion.
- Its public dependency `Sheaf.CategoryTheory.DgBimoduleModels`:
  `BalancedTensorModel` and `shiftedElement`; read the complete module, including
  `IsTensorShift` and `BimoduleHomModel` for the comparison conventions.
- Its public dependency `Sheaf.CategoryTheory.DgAlgebraDerivedCategory`:
  `Algebra`, `RightModule`, `Derived`, `Q`, `DerivedStructure`, `ShiftComparison`,
  and the `shiftIso` field; read the complete module.
- `WeilConjectures.CategoryTheory.CompactObject`, `CategoryTheory.IsCompactObject`:
  read the definition and docstring. The example Sheaf module is withdrawn,
  and this node's current record points to this identical upstream definition.
- The metatheoretic record for `def-weil-size-convention` has no declaration;
  universes are stated explicitly as its note requests.
- Proof-only import `Sheaf.CategoryTheory.DgAdjunctionCompactUnit`,
  `CategoryTheory.DgAlgebra.adjunction_unit_isIso_of_compact_regular`: read its
  statement/docstring; matches step 5 without target generation.
- Proof-only import `Mathlib.CategoryTheory.Adjunction.Limits`,
  `CategoryTheory.Adjunction.leftAdjoint_preservesColimits`: read its statement
  and docstring for step 1.
- The other five DG proof prerequisites currently have no recorded Lean module
  or Mathlib match, so there is no proof-only import for them yet:
  `lem-sfb-dg-derived-admissible-triangles`,
  `lem-sfb-dg-sequential-colimit-triangle`,
  `lem-sfb-dg-semifree-bimodule-tensor-computation`,
  `lem-sfb-dg-free-module-hom-cohomology`, and `lem-sfb-dg-free-shift-derived-hom`.
  Their statements were read; the theorem docstring records their uses.

Edge cases checked before drafting:

- k = 0 retains the ordinary left action; all negative k remain quantified.
- N = 0 forces every H^k(A) to vanish through the additive-equivalence hypothesis;
  it does not assert full faithfulness of a zero functor from a nonzero source.
  Zero and acyclic algebras/modules are admitted.
- Compactness includes the empty coproduct through the existing definition.
  No nonempty or countable index restriction is added.
- Noncommutative A and B are admitted. Homogeneous right linearity has no
  extraneous Koszul sign; the cycle's left multiplication obeys the shifted
  differential convention already fixed by `ShiftComparison`.
- Boundary cycles map to zero because φ is additive and factors through the
  actual cohomology quotient. Replacing a shift representative does not change
  the mathematical assertion, since its isomorphism is included in e.

Searches (2026-10-24; msearch.py with group NC and this item):

- LeanFinder: `Derived tensor with a compact differential graded bimodule is fully
  faithful when the left action identifies all cohomology with derived self
  extensions`. Eight hits, chiefly derived singleFunctor full/faithfulness,
  K-projective Hom comparison, derived functor linearity and Tor. None states
  the DG compact-bimodule criterion.
- Loogle: `"IsCompactObject", "FullyFaithful"`. Zero hits.
- Mathlib grep via msearch: `DGAlgebra|DGModule|[Cc]ompact.*[Bb]imodule|[Bb]imodule.*[Ff]ully`,
  subdirectory CategoryTheory. Zero hits.
- LeanSearch: `A compact differential graded bimodule with the correct self
  extension groups induces a fully faithful derived tensor functor`. Eight hits
  about extension functors, ordinary fully faithful functors, condensed locally
  constant modules and derived Qh. None matches this statement.
- rg in `lean/WeilConjectures` for `compact.*bimodule|bimodule.*fully|DgAlgebra|dg-compact-bimodule-full-faithfulness`:
  zero hits. rg in `lean/Sheaf` for compact-bimodule/full-faithfulness and
  self-extension names found only unrelated two-term ordinary-complex
  self-extension lemmas. No existing statement matches this item.
- rg across `lean/Sheaf`, `lean/WeilConjectures`, and Mathlib's monoidal directory
  for `bimoduleRightModule|rightModule.*Bimod|Bimod.*rightModule|actRight.mop|mop N.X`:
  zero hits. Read Mathlib's Bimod and Mod definitions to construct the restriction
  directly, rather than replacing it by an unspecified object.

Validation: scompile.py compiled this file as both a sandbox module and its
library module, with no errors or warnings (6.5 s and 8.5 s respectively).
`autoImplicit` is false and the only universe is explicitly declared.

## Second reading by NC

Worker readback, not an independent agent review: the dispatcher explicitly
forbids starting agents and assigns the independent reading to the maintainer.
Reopened the source statement and Lean signature. The two substantive hypotheses
are compactness of N and the action-induced additive isomorphism in every degree;
all other binders specify the DG objects, their standard derived structures,
shift representatives and the universal derived tensor. Verified in particular
that the action is pinned on every cycle and every homogeneous element, that
`φ` is applied to the actual cohomology quotient, and that the conclusion covers
all morphism sets. Checked the helper preserves N's actual right action. No
mismatch was found and no source statement or dependency record was changed.
