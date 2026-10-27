## Worker report

The module `Sheaf.AlgebraicGeometry.UnramifiedDiagonalSingletonFieldCover` states
`CategoryTheory.exists_unramified_diagonal_singleton_field_cover`, with a single
`sorry` proof, exactly for the relative-base version of Stacks Tag 06N0. Read the
full source lemma and proof in stacks-morphisms.tex, plus Tag 050N (1), which
identifies the relative DM condition with the absolute condition. Read the latest
blueprint direct-images proof in sk-thm-sf-ctf-stability: this is a supporting
lemma, not the unit's own statement. There is no statement correction.

Hypotheses and clauses:

- An arbitrary scheme S is `{S : Scheme.{u}}`. There is no Noetherian hypothesis
  on S. The stack is `F : BasedCategory.{v, w} (Over S)`; the total category's
  object and arrow universes remain independent of u.
- Stack in groupoids with effective etale descent is `hstack : IsModuliStack F`.
  Its definition includes `IsFibredInGroupoids F` and descent of cartesian sections.
- Algebraic-space-representable diagonal is `hdiag : HasAlgebraicSpaceDiagonal F`.
- A smooth surjective scheme atlas is explicitly bound as `U`, `atlas`, and
  `hatlas : IsSmoothModuliAtlas F U atlas`. An explicit arbitrary witness of the
  existential atlas condition does not assume an etale atlas. Representability,
  smoothness and surjectivity of its actual scheme base changes are retained.
- Reduced and locally Noetherian mean this same atlas satisfies
  `hreduced : ∀ x : U.left, _root_.IsReduced (U.left.presheaf.stalk x)` and
  `hnoetherian : IsLocallyNoetherian U.left`. These are precisely the local-ring
  reducedness and the recorded Mathlib Noetherian scheme notion.
- Exactly one point is `hsingleton`: there exists a field K, a structural map s
  and an object x; for every field L, structural map t and object y, there is a
  common extension E over S and a `Nonempty (ModuliTwoIso ...)` comparing their
  actual pullbacks. Scheme maps between field spectra are unital field maps in
  the opposite direction, hence injective, so the common field extension clause
  is exact. The existence clause rules out an empty point set. This follows the
  already recorded flat-field-cover theorem's identical singleton interface.
- The relative unramified diagonal is
  `hunramified : HasUnramifiedModuliDiagonal F`. Its definition retains both
  projections from the represented 2-fibre product to `T ⨯ U` in `Over S` and
  tests the resulting map on all etale scheme charts using `IsUnramified`.
- The conclusion binds a real `K : Type u`, `Field K`, `s : Spec (.of K) ⟶ S`
  and `a : BasedFunctor (discreteModuli (yoneda.obj (Over.mk s))) F`. No perfectness,
  algebraic closedness, finite extension or separability of K is assumed.
- For every scheme T and actual map t into F, the conclusion supplies a space Z
  and projection p with `HasSpaceBaseChange a T t Z p`. This is exactly
  representability by algebraic spaces, written out rather than repeated as a
  redundant conjunct. `SpaceMapIsEtale Z T p` and `SpaceMapIsSurjective Z T p`
  assert etaleness and surjectivity of that very projection. All scheme tests,
  including the empty scheme and nonreduced schemes, remain quantified.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `IsModuliStack`, `HasAlgebraicSpaceDiagonal`, `discreteModuli`,
  `discreteModuliMap`, `ModuliTwoIso`, `HasSpaceBaseChange`,
  `SpaceMapIsEtale`, `SpaceMapIsSurjective` and their full definitions/docstrings.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsEtale` and `IsRepresentableWith`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsSmoothModuliAtlas` and
  `SpaceMapIsSmooth`. Added its landed owning node
  `def-sfb-algebraic-moduli-stack` to stmt_deps.
- `Sheaf.AlgebraicGeometry.OpenModuliSubstack`:
  `HasUnramifiedModuliDiagonal`, `SpaceMapIsUnramified`, `moduliTwoFiberSnd`.
  Added its landed owning node `def-sfb-open-moduli-substack` to stmt_deps.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: `AlgebraicGeometry.IsUnramified`,
  the conjunction of local finite type and open-immersion diagonal.
- Mathlib `Algebra.Field.Defs`: `Field`; `AlgebraicGeometry.Noetherian`:
  `IsLocallyNoetherian`; `AlgebraicGeometry.Morphisms.Smooth`: `Smooth`;
  `AlgebraicGeometry.Morphisms.Etale`: `Etale`.

All the original statement dependencies are used through the public import
closure, including the original scheme smooth, unramified and etale notions.
Plain proof imports are the recorded modules of
`lem-sfb-singleton-stack-flat-lfp-field-cover`,
`lem-sfb-etale-smooth-atlas-fppf-descent`,
`lem-sfb-stack-chartwise-smooth-etale-calculus`, and
`lem-a1-finite-flat-affine-relation-quotient`. The remaining proof dependencies
currently have no Lean record: `lem-sfb-fppf-groupoid-stack-presentations`,
`lem-sfb-field-groupoid-identity-finite-relation`,
`lem-sfb-divide-finite-flat-subgroupoid`,
`lem-sfb-representable-fppf-etale-open-descent`, and
`lem-sfb-groupoid-open-unit-etale`. They are named in the complete proof docstring
and need imports when their statements land; they supply no missing notion in
this item's signature.

Edge cases checked before drafting: the empty stack is excluded by the
existential field object, as required by exactly one point; the empty base
cannot satisfy this hypothesis. A field spectrum itself satisfies the intended
identity case. Classifying stacks of finite etale groups retain their
nontrivial automorphisms: the conclusion is a cover, not a scheme representation.
Purely inseparable extensions and imperfect fields are allowed. Nonreduced
atlases are excluded only by the prescribed reducedness hypothesis; atlas
reducedness is tested stalkwise. The base need not be reduced or Noetherian.
All field/test-scheme universes equal the scheme universe u; no independent
smaller test universe makes the hypotheses vacuous. v and w are arbitrary.

Searches made using the prescribed msearch.py wrapper:

- LeanFinder: `A reduced locally Noetherian algebraic stack with one point and
  unramified diagonal has a surjective etale map from the spectrum of a field`:
  8 hits, all scheme/ring etale or formally unramified facts, no stack theorem.
- Loogle: `AlgebraicGeometry.Scheme, AlgebraicGeometry.Etale`: 12 hits,
  the scheme Etale class and permanence/relative-dimension facts, no match.
- Mathlib grep: `singleton.*[Ss]tack|residualGerbe|[Uu]nramified.*[Dd]iagonal`
  in AlgebraicGeometry: 1 hit about formally unramified affine diagonals,
  no stack statement.
- LeanSearch: `A reduced locally Noetherian algebraic stack with a singleton point
  set and unramified diagonal admits a surjective etale field spectrum cover`:
  8 hits, including IsLocallyNoetherian, open diagonals, stalkwise reducedness and
  etale loci. None states the algebraic-stack assertion.
- Direct rg of lean/WeilConjectures and lean/Sheaf for singleton-stack,
  residualGerbe, and unramified/singleton combinations found only the distinct
  flat lfp field-cover theorem and unrelated singleton-cover comments. The flat
  theorem lacks etaleness and the diagonal hypothesis, so is no existing match.
- grep of the exact item id in lean/WeilConjectures returned no match.
  The name index had no existing singleton cover or diagonal-atlas predicate
  declaration that replaces this theorem. Existing stack predicates were reused.

Validation: prescribed scompile.py completed successfully against the live
server sources (3.7 seconds, 60-second per-file limit); no server compiler error
or unexpected warning. The local first attempt reported disk exhaustion and
scompile.py automatically used its successful server confirmation.

No new nodes, dependency replacements, statement correction, or mathematical
dispute. Only lean and the two landed definition-node additions to stmt_deps
change in the item copy.

## Second reading by Q49

This is a separate self-reading of the saved node copy and saved Lean file;
the dispatcher forbids starting another agent and assigns the maintainer's
independent review after delivery. It is not claimed as an independent review.

Matched the arbitrary base, the stack and diagonal hypotheses, the same smooth
surjective atlas with both reduced and locally Noetherian properties, and the
existence-plus-common-field-extension singleton condition against the node.
Matched the relative diagonal to the existing two-projection product-over-S
predicate, rather than the absolute diagonal or an assumed etale atlas.
Matched the conclusion's field spectrum, map a, and every scheme-base-change
space/projection with representability, etaleness and surjectivity. No missing
clause or extra field/base hypothesis was found. No changes were needed after
this reading. The sole postponed proof is the named item theorem; all referenced
definitions are existing real constructions. The six source proof steps are
present in its docstring, with the P-invariant field and both descent covers
retained. The JSON signature is extracted verbatim from the saved Lean file.
