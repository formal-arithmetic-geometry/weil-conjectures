## Worker report

The module `Sheaf.AlgebraicGeometry.InvariantOpenSubstackDescent` states
`CategoryTheory.invariantOpenSubstackDescent`, with its only proof postponed by `sorry`.
Two actual constructions, `openAtlasScheme` and `openAtlasSchemeι`, give an atlas open its
structural map to S and its canonical inclusion into P. Neither chooses data or postpones
construction. Their docstrings belong to this node. No new definition node is needed:
these are just the canonical scheme and arrow for the open already in the statement.

Source read: `literature/stacks-project/stacks-properties.tex`, lemma-substacks-presentation
(Tag 0507), lines 1809ff, including its factorization proof and explicit open case;
`literature/stacks-project/algebraic.tex`, definition-algebraic-stack, lines 1289ff,
including its discussion of the equivalent etale-stack convention. The newest blueprint
unit was read at `literature/blueprint/latest/blueprint/sec-six-functors-basics/`
`sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.md`. This auxiliary lemma
is not the statement of that unit. No correction is made to either statement.

Hypotheses and clauses, matched individually:

- Base scheme S: `{S : Scheme.{u}}`. Every atlas, scheme test and scheme arrow is over
  exactly this base, via `Over S`.
- Algebraic stack X: `F : BasedCategory.{v₁, w₁} (Over S)` and
  `hF : IsAlgebraicModuliStack F`. The recorded definition asserts etale stack descent,
  algebraic-space diagonal and existence of a smooth surjective scheme atlas.
- Specified smooth surjective scheme atlas p:P→X: `P : Over S`,
  `p : BasedFunctor (discreteModuli (yoneda.obj P)) F`, and
  `hp : IsSmoothModuliAtlas F P p`. This is precisely the scheme-base-change condition
  in the final sentence of the node: every test has an algebraic-space presentation
  whose actual projection is smooth and surjective on scheme-chart points.
- Strictly full open substacks: the existing `OpenModuliSubstack F`. Its property is
  stable under every arrow of the fibred groupoid, hence under isomorphisms in both
  directions, and the subcategory and inclusion are full. Every scheme test has a
  representing open immersion, with comparison over that test scheme. For an ambient
  stack this scheme-test condition also makes the selected full subcategory a stack;
  no unrecorded notion is substituted.
- Atlas open subschemes: `V : P.left.Opens`, using Mathlib's canonical restricted scheme.
  Invariance `s⁻¹V=t⁻¹V` on R=P×_X P is expressed by all its scheme-valued tuples:
  `∀ (T : Over S) (a b : T ⟶ P), Nonempty (ModuliTwoIso (...a...p) (...b...p)) →
  a.left ⁻¹ᵁ V = b.left ⁻¹ᵁ V`. Such tuples are exactly scheme maps to the 2-self-relation.
  Equality on all these tests means equality of open subspaces as subfunctors, rather
  than merely testing rational points of one field. For opens the canonical restricted
  scheme is determined by its open subset, so equality of these inverse-image opens
  is equality of their open subschemes, including their sheaves.
- Bijection by pullback: `∃ e : OpenModuliSubstack F ≃ {V // ...invariance...}`.
  The next condition identifies this particular e with the atlas pullback, so it
  cannot be an unrelated bijection between two types.
- Inclusion preservation: `W.IsContainedIn Z ↔ (e W).val ≤ (e Z).val`. This says that
  e and its inverse preserve inclusion, exactly as in the node's proof step 7.
- Corresponding pair P×_X W=V: the existential comparison functor c has domain the
  discrete groupoid represented by `openAtlasScheme P (e W).val`, codomain
  `moduliTwoFiberProduct p (fullModuliInclusion F W.property)`, is an equivalence,
  and its first projection is `ModuliTwoIso` to the discrete canonical inclusion
  `openAtlasSchemeι P (e W).val`. Thus the identification is over P, not an abstract
  equivalence that forgets the projection. It uses no chosen auxiliary map.
- Every algebraic-stack morphism f:Y→X: `G : BasedCategory.{v₂, w₂} (Over S)`,
  `IsAlgebraicModuliStack G`, `f : BasedFunctor G F`. Source and target object/morphism
  universes are independent; no representability of f or size equality is required.
- f factors through W: an actual `g : BasedFunctor G W.category`, together with a
  `ModuliTwoIso` from its composite with the full inclusion to f.
- Atlas-pullback map factors through V iff f does: the right side of the final `↔`
  supplies an actual based functor from `moduliTwoFiberProduct p f` to the discrete
  groupoid of the canonical open scheme V, with its composite inclusion 2-isomorphic
  to `moduliTwoFiberFst p f`. The factors are ordered P×_X Y to use the existing first
  projection; its tuple description is the symmetric 2-fibre product Y×_X P→P.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Scheme.Opens`; and its canonical restricted open scheme and `Opens.ι`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsFibredInGroupoids`, `ModuliTwoIso`, `moduliTwoFiberProduct`,
  `moduliTwoFiberFst`, `discreteModuli`, `discreteModuliMap`, `IsModuliStack`,
  `HasSpaceBaseChange`, `HasAlgebraicSpaceDiagonal`, `SpaceMapIsSurjective`.
  Their signatures and docstrings were read, including the actual base projection
  and full iso-comma construction, not merely their names.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsRepresentable`, `IsEtale`, `IsSurjective`,
  `IsAlgebraicSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`;
  it is the current name in the dependency record, not the deprecated IsSmooth alias.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `CategoryTheory.IsAlgebraicModuliStack`,
  `IsSmoothModuliAtlas`, `SpaceMapIsSmooth`.
- `Sheaf.AlgebraicGeometry.OpenModuliSubstack`: `CategoryTheory.OpenModuliSubstack`,
  its `category`, `IsContainedIn`, `fullModuliSubcategory`, `fullModuliInclusion`.
- The statement dependencies gain the already-landed `def-sfb-algebraic-moduli-stack`
  and `def-sfb-open-moduli-substack`. This is authorized by brief-stage2 section 5,
  "STMT_DEPS MAY GAIN LANDED NODES". They already define notions described inline in
  the node, so neither its mathematical statement nor proof changes. No dependency
  modules are rewritten or duplicated.
- Proof-only imports are exactly the stated proof dependencies:
  `Mathlib.AlgebraicGeometry.OpenImmersion` (`IsOpenImmersion`),
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage`
  (`openSubspace_points_orderIso`),
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatLfpUniversallyOpen`
  (`universallyOpen_of_flat_of_locallyOfFinitePresentation`),
  `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`
  (`stack_chartwise_implications`, `surjective_moduli_iff_chartwise`), and
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`
  (`fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`). Their recorded signatures
  and source docstrings were inspected. All are plain imports.

Edge cases checked before finalizing: the empty stack and empty atlas are allowed;
V=∅ and V=P give the empty and whole substacks. No nonemptiness binder excludes either.
For identity atlases the relation condition is automatic and the bijection is the
usual classification by opens. Stacks with nontrivial automorphisms retain their
comparison isomorphisms and all arrows: the formulation does not replace groupoids by
isomorphism classes. Nonrepresentable f is allowed. Nilpotents are retained in canonical
open restrictions, whose structure is not replaced with a reduced subscheme. No base
Noetherianity, quasi-compactness, separation, characteristic or finiteness is imposed.
No statement fault or STATEMENT-DISPUTED flag.

Searches for an existing statement, all made using the prescribed wrappers/read paths:

- msearch leanfinder: "Open substacks of an algebraic stack correspond to invariant open
  subschemes in a smooth surjective atlas, with factorization detected after atlas
  pullback". Eight results concern scheme/ring/manifold opens, none this statement.
- msearch leansearch: "invariant open subschemes descend to open substacks of algebraic
  stacks". Eight results concern `Scheme.Opens`, open immersions and scheme descent,
  none the algebraic-stack theorem.
- msearch loogle: "OpenModuliSubstack, IsAlgebraicModuliStack". Zero results; Loogle
  does not index the project's OpenModuliSubstack. A follow-up query used the known
  Mathlib name `AlgebraicGeometry.Scheme.Opens`; its twelve hits were Scheme.Opens and
  basic scheme-open constructions, not the stack correspondence.
- msearch grep: `OpenSubstack|invariant.*[Oo]pen|open.*[Ss]ubstack`, Mathlib's
  AlgebraicGeometry subdirectory: zero hits.
- rg in `lean/WeilConjectures` and `lean/Sheaf`: searched the item id,
  `OpenModuliSubstack`, `invariant_open_substack`, `IsAlgebraicModuliStack`,
  `openAtlasScheme`, and `invariantOpenSubstackDescent`. Existing consumers cite the
  missing theorem, but no module states it. The DM point-topology classification is
  narrower and lacks this atlas/factorization statement; the closed-substack descent
  theorem concerns ideal sheaves, not opens. Existing notion modules were reused.
- Searched `dag/lean_names_upstream.json` for the proposed declarations; no conflicts.
  `tools/blueprint_refs.py search 'invariant open'` returned zero blueprint nodes.
  No search result was treated as an existing Lean theorem without reading its source.

Validation: prescribed scompile.py compiled this file separately as both
`Sheaf.Stage2.Sandbox0` and `Sheaf.AlgebraicGeometry.InvariantOpenSubstackDescent`,
without errors or warnings. The delivered Lean file starts in module mode, explicitly
binds every universe and variable, uses public statement imports and plain proof imports,
and has no line over 100 characters. Its only theorem has proof exactly `by sorry`.

## Second reading by Q33

A separate in-thread rereading compared the node with the final module and all conclusion
clauses. No other agent was started, as the dispatch explicitly forbids it; this does not
claim an independent reviewer has already approved the statement. The maintainer's
independent delivery review remains the next review.

The rereading checked that the atlas hypothesis controls the actual projection, the
invariance condition quantifies over all scheme tuples and 2-isomorphisms, the bijection
is tied to the actual base change over P, both inclusion directions are present, and the
factorization equivalence has arbitrary algebraic-stack source with independent universes.
The RHS projection from P×_F G was checked explicitly against the order of arguments to
`moduliTwoFiberProduct`; its first projection is the required map to P. The canonical
open scheme arrow is a real `Over.homMk V.ι`, not an arbitrary morphism. No mathematical
mismatch was found. The only metadata change outside lean is registering the two existing
notion nodes in stmt_deps under the explicit section-5 authorization.
