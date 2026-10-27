## Worker report

The module Sheaf.AlgebraicGeometry.ProjectivePGLInvariantQuotient states
AlgebraicGeometry.PGLLinearization.projective_pgl_invariant_quotient, with one
postponed proof and no new definitions. Only the item's lean field changes.

Source read: Alper, Adequate moduli spaces and geometrically reductive group
schemes, published PDF https://content.algebraicgeometry.nl/2014-4/2014-4-022.pdf,
printed pp.490--491, projective semistable quotient and the Main Theorem;
the node specifies Theorems 9.1.4, 9.7.6, 6.3.3 and 5.3.1(2), with
Proposition 5.2.9(3). The proof docstring follows all eight DAG proof steps,
including the zero-divisor localization argument and the saturated-atlas
argument after arbitrary base change.

Hypothesis and clause correspondence:

- Any field k: `(k : Type u) [Field k]`. There is no characteristic restriction.
- Matrix size r >= 2: `(r : ℕ) (hr : 2 ≤ r)`.
- A k-scheme Z: `Z : Over (Spec (.of k))`. Its specified structure morphism is
  `Z.hom`.
- Projective and finite type: `IsHProjective Z.hom` and
  `LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom`.
- An invertible module A: `L : Z.left.Modules` and `[L.IsInvertible]`.
- Ample: `Scheme.Modules.IsAmple Z.left L`. This is the absolute notion of the
  recorded ample node, not a second relative ampleness predicate. The current
  server source was read with `scompile.py --source
  WeilConjectures.AlgebraicGeometry.Ample` to confirm the signature.
- PGL action with its linearization: `D : Action k r Z L`. This recorded
  interface is natural GL_r actions on all test schemes with scalar-trivial
  action and line lift, equivalently fppf descent to PGL. No assumption that
  arbitrary PGL-valued points globally lift to matrices is made.
- The geometric semistable open is supplied by `∃ U : Z.left.Opens` together
  with the equivalence, for every algebraically closed field extension Ω and
  every `x : fieldTest k Ω ⟶ Z`, between membership of its underlying point in
  U and `D.IsSemistable Ω x`. Thus U is the specified locus, not an arbitrary
  smaller invariant open. Its invariance follows from that characterization
  and the action laws. Existence of the open is retained in the conclusion.
- The source of q is exactly `Over.mk (U.ι ≫ Z.hom)`.
- A projective finite-type k-scheme Q is `Q : Over (Spec (.of k))` with
  `IsHProjective Q.hom ∧ LocallyOfFiniteType Q.hom ∧ QuasiCompact Q.hom`.
- The arrow q is an Over morphism, so is a k-morphism. Surjectivity and finite
  type are `Surjective q.left ∧ LocallyOfFiniteType q.left ∧ QuasiCompact q.left`.
- Affineness is `IsAffineHom q.left`, whose definition is exactly affine
  preimages of every affine target open.
- Invariance is equality `y ≫ q = x ≫ q` whenever y followed by the open
  inclusion is `D.act W g` of x followed by that inclusion, for every test
  k-scheme W and matrix g. Yoneda and fppf descent turn this into the action
  morphism equality q a = q pr₂. Since the open is invariant, its translated
  point exists; the conditional formulation does not restrict invariance.
- Every T -> Q: `∀ (T : Over (Spec (.of k))) (t : T ⟶ Q)`. An arbitrary
  scheme with a map to Q has the unique induced k-structure, so this covers
  exactly the node's arbitrary base changes; no flatness or finiteness occurs.
- X_T is the canonical `pullback q t` in Over. Forgetting to schemes creates
  this pullback, so its projections are the stated X_T -> U and X_T -> T.
- A closed subscheme is any `C : Over (Spec (.of k)))` with
  `i : C ⟶ pullback q t` and `IsClosedImmersion i.left`. Every closed subscheme
  inherits its k-structure, so this quantification loses none.
- Preservation of its defining ideal is rendered on all test schemes: for
  each g and x in C(W), there is y in C(W) with the same projection to T and
  with its projection to Z equal to the translate of x. These two equalities
  specify the action on the fibre product. For a closed immersion, factorization
  of all such translated test points through i is precisely preservation of
  the ideal, by Yoneda. Taking W to be the group times C detects the universal
  action morphism, including nilpotents. Since GL -> PGL is fppf surjective,
  these matrix tests detect the full PGL_T action. The inverse element gives
  preservation in the other direction too.
- The conclusion `IsClosed (Set.range (i ≫ pullback.snd q t).left)` is exactly
  closedness of the image of |C| in |T|.
- No reducedness, stabilizer, or linear reductivity assumptions are present.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: Field.
- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- WeilConjectures.AlgebraicGeometry.Morphisms.Projective:
  AlgebraicGeometry.IsHProjective (finite projective-space embedding).
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType, with
  QuasiCompact from Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- WeilConjectures.AlgebraicGeometry.Modules.Invertible:
  AlgebraicGeometry.Scheme.Modules.IsInvertible.
- WeilConjectures.AlgebraicGeometry.Ample:
  AlgebraicGeometry.Scheme.Modules.IsAmple.
- Sheaf.AlgebraicGeometry.PGLLinearizedPolarization:
  AlgebraicGeometry.PGLLinearization.Action, Matrices, fieldTest, and
  Action.IsSemistable; Action.IsInvariantSubscheme was read to check the same
  all-test-scheme convention. The fibre-product invariance is written inline
  to require that the T-coordinate stays fixed, without defining a new action.
- Sheaf.AlgebraicGeometry.HilbertPluckerPGLLinearization:
  AlgebraicGeometry.exists_hilbert_plucker_pgl_linearization and
  HilbertPlucker.Presentation.semistable_points were read with their docstrings;
  they use the same positive-degree invariant-section semistability convention
  through GroupSchemeLinearization.Linearization.IsSemistable. The general
  action used here is the explicitly recorded PGLLinearization.Action.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: pullback,
  pullback.fst and pullback.snd.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: IsClosedImmersion.
- Mathlib.AlgebraicGeometry.Morphisms.Affine: IsAffineHom.

All recorded proof-dependency modules are imported, using plain imports when
only the postponed proof needs them. Mathlib proof leaves supply the proper,
immersion, flatness, Noetherian, Proj, gluing and affine-chart APIs. The two
proof-only nodes lem-sfb-pgl-reductive-structure and
lem-sfb-power-lifting-adequate-affine-quotient have no recorded module in the
read clone; they add no imports. No statement dependency is missing.

Edge cases checked before writing: Z empty and the semistable locus empty
permit empty Q; the empty closed subscheme has empty closed image; T is allowed
empty, nonreduced, non-Noetherian and nonflat over Q; Z can be nonreduced;
r = 2 is included; all positive characteristics, including characteristic
dividing r, are allowed; nontrivial degree-zero section algebras are permitted
because Q is not forced to have constant algebra k. Schemes, fields and all
scheme-valued tests use the common universe u required by the recorded action;
no extra smallness or universe equality assumption is imposed.

Searches actually run for this item:

- msearch.py leanfinder: "A projective semistable PGL quotient is affine
  surjective and universally sends invariant closed subschemes to closed
  subsets". Eight hits, on affine-space surjectivity, Proj properness,
  Proj-to-Spec charts and closed immersions; no exact quotient theorem.
- msearch.py loogle: `"IsAffineHom", "Surjective"`: zero hits.
- msearch.py leansearch: "Projective semistable reductive group quotient maps
  invariant closed subschemes to closed subsets after every base change".
  Eight hits on stability of morphism properties under base change, ordinary
  universal closedness and additive-group quotients; no exact match.
- msearch.py grep, AlgebraicGeometry:
  `semistab.*quotient|invariant.*quotient|PGL`: three irrelevant Gluing.lean
  matches involving toTopGlueData; no GIT theorem.
- rg over lean/WeilConjectures and lean/Sheaf:
  `semistab.*quotient|invariant.*quotient|pgl_invariant_quotient` and item-id
  search in WeilConjectures. No upstream item declaration. Related project
  results ProjectivePGLStableQuotient and PGLSemistableAffineQuotientGluing
  assume stable semistable points and assert different quotient properties;
  neither states this arbitrary-stabilizer universal closed-image assertion.

No statement correction, dependency repair or new node was required.
No STATEMENT-DISPUTED issue was found.

Validation: scompile.py compiled both the sandbox and the library-form module
successfully (51.9 s and 4.8 s), with no diagnostic warnings or errors.

## Second reading by Q90

The dispatcher explicitly forbids starting another agent; this is a separate
second pass by the same worker, with independent maintainer review to follow.
I reread the node, its recorded action definitions, and the actual delivered
signature. Field, r >= 2, projectivity, finite type, invertibility and absolute
ampleness each occur explicitly. The existential U is uniquely pinned on
geometric points and q has that whole open as source. Q has both required
properties; q has all four required properties (surjective, invariant, finite
type, affine). The arbitrary base-change clause fixes the T-coordinate during
translation and tests factorization through the closed subscheme on every
scheme, so does not weaken ideal invariance to support invariance. Its final
range is the image of C in T, with no extra flatness assumption. I checked the
Over pullback projections and the original module's IsSemistable signature
against the recorded source. No mismatch was found and no signature change
was made during this pass.
