## Worker report

The module `Sheaf.AlgebraicGeometry.BertiniIrreducibleMember` states Stacks Tag 0G4F,
`exists_open_geometricallyIrreducible_linearSystemMember`, with `sorry`, and constructs its
member ideal in `linearSystemMemberIdeal`. No theorem is proved. No statement correction,
new independent notion, or dependency repair is needed. Only the item's `lean` field changes.

I read the full source statement and proof in `literature/stacks-project/more-morphisms.tex`,
lines 9055–9160, and Situation 0G47 in `varieties.tex`, lines 10909ff. The source-place string
in the node still says 0FD3, but the actual reference is 0G47 as the node's existing review
already records. The module cites the correct source tag; this source-field discrepancy is
reported here without an unauthorized metadata edit.

Clause-by-clause reading:

- A field k: `(k : Type u) [Field k]`.
- A k-scheme Y: `(Y : Scheme.{u}) [Y.Over (Spec (.of k))]`, with structure map
  `Y ↘ Spec (.of k)`.
- Finite type: `LocallyOfFiniteType` and `QuasiCompact` of that structure map.
- Geometrically irreducible: `GeometricallyIrreducible` of that same structure map.
  This includes geometric nonemptiness and imposes no geometric reducedness.
- The invertible O_Y-module: `(L : Y.Modules) [L.IsInvertible]`.
- The finite-dimensional vector space: `(V : Type v) [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]`. Its universe is independent of the scheme's.
- The natural k-action on global sections is the explicit `letI` restricting scalars via
  `Scheme.globalSectionsRingHom k`. This specifies the canonical action, rather than
  assuming an unrelated action. There is no data `let` in the statement.
- The linear section map is `ψ : V →ₗ[k] Γ(L, ⊤)`.
- Hypothesis (i) is the first existential implication: three vectors and
  `W : TopologicalSpace.IrreducibleCloseds Y`; `Maximal` says W is a maximal irreducible
  closed subset contained in the intersection of the supports of the two zero schemes.
  This is exactly a component of that closed intersection: closures of irreducible subsets
  stay inside a closed intersection, so maximal irreducible subsets are closed.
  The next conjunct is `¬ (W : Set Y) ⊆ ...zeroLocus.support` for v₁, and the final conjunct
  is `Order.coheight W = 2`. On irreducible closed sets ordered by inclusion, coheight
  is exactly the supremum of lengths of strict ascending chains starting at W, as defined
  in the node. No dimension subtraction or purity assumption is substituted.
- Hypothesis (ii) quantifies over every irreducible closed B maximal among those contained
  in `⋂ w : V, ...zeroLocus.support`; its conclusion is `2 ≤ Order.coheight B`.
  The intersection is the underlying closed set of the scheme-theoretic base locus.
  The hypothesis is vacuous when that set is empty.
- A basis is specified by `∀ (r : ℕ) (b : Module.Basis (Fin r) k V)` after the two hypotheses.
  This is the coordinate choice in the node's definition of generality, not an additional
  mathematical hypothesis on V. Every finite-dimensional V admits such a basis. Requiring
  the conclusion in every basis is equivalent to the given definition, since a change of
  basis is a k-linear automorphism of affine r-space, preserves nonempty opens, and gives
  the same sections after changing coordinates.
- The nonempty Zariski open is `∃ U : (Spec (.of (MvPolynomial (Fin r) k))).Opens,
  (U : Set _).Nonempty ∧ ...`. This is affine r-space, with polynomial coordinate ring.
- Every extension and every vector in its coordinates are quantified as
  `∀ (K : Type u) [Field K] [Algebra k K] (a : Fin r → K)`.
  `Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := k) a).toRingHom)` is exactly
  the corresponding K-point. Its range being contained in U says that point belongs to U;
  Spec K has one point, so this imposes precisely the membership condition in 0G47.
- `linearSystemMemberIdeal ... L (fun i ↦ ψ (b i)) K a` is constructed on
  `pullback (Y ↘ Spec k) (Spec.map (algebraMap k K))`, using `tensorPullback` along fst.
  The normalized adjunction unit sends each section to `1 ⊗ s`. The function corresponding
  to `a i` is `(Scheme.ΓSpecIso (.of K)).inv (a i)`, pulled back by snd.appTop.
  The finite sum of these products is the prescribed section `∑ a_i ψ(b_i)` of L|Y_K.
  `@id` only makes its global-section type explicit at the definitional equality
  between sections of pushforward over top and sections over the preimage of top.
  Applying the existing `homOfGlobalSection` and `Hom.zeroLocus` gives exactly its zero ideal.
- The conclusion `GeometricallyIrreducible (member.subschemeι ≫ pullback.snd ...)` is
  geometric irreducibility of this very zero scheme over K, not merely of its topological
  support over k or of one geometric fibre. The field-universe convention is the same
  as the recorded `def-pc-geometrically-irreducible` Mathlib match; larger extensions
  reduce to small generated subextensions for these finite-type schemes.

Recorded dependency declarations read and used:

- The two scheme/morphism-convention nodes explicitly fix no new declaration. Their named
  notions are Mathlib `Scheme`, `LocallyOfFiniteType`, `QuasiCompact`, and scheme over-base
  structure. I read the finite-type and quasi-compact class signatures/docstrings.
- `def-weil-irreducible-components`: `Mathlib.Topology.Irreducible`,
  `irreducibleComponents X = {s | Maximal IsIrreducible s}`. Its equivalent closed-subset
  maximality is used above with `TopologicalSpace.IrreducibleCloseds` (Mathlib's existing
  type, not a new definition). I read both definitions and the closedness result.
- `def-pc-geometrically-irreducible`: `Mathlib.AlgebraicGeometry.Geometrically.Irreducible`,
  `AlgebraicGeometry.GeometricallyIrreducible (f : X ⟶ Y)`; read its full class signature
  and all-field base-change docstring.
- `def-sc-invertible-module`: `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`; read its local-unit definition.
- `def-pc-zero-scheme`: `WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus`,
  `AlgebraicGeometry.Scheme.Modules.Hom.zeroLocus`; read its definition and docstring,
  including its interpretation for O_Y → L and the need for invertibility.
- `def-pc-base-change`: `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`;
  read the current source with `scompile.py --source`, including its explicit statement
  that schemes use `Limits.pullback`, fst and snd, and module base change uses
  `Scheme.Modules.tensorPullback`. The older local checkout lacks this published module.
- The helper additionally uses the published
  `WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction`,
  `Scheme.Modules.exists_tensorPullbackAdjunction`, whose full normalized unit formula
  was read with `scompile.py --source`; and
  `WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator`,
  `Scheme.Modules.homOfGlobalSection`, whose implementation was read.

The stated proof dependencies are imported without `public`: geometric-irreducibility
shrinking, reduction nilradical nilpotence, finite-type-domain maximal-chain length,
Noetherianity, and the height bound. The four new algebraic Bertini inputs and generic-point
criterion have no recorded declarations yet, so no import is available for those proof-only
nodes. Their full natural-language use is retained in the eight-step theorem docstring.
No statement dependency is missing.

Edge cases checked: the empty Y is excluded by geometric irreducibility. Dimension below two,
V=0 and r<3 cannot satisfy (i); nevertheless the syntax permits them. For ψ=0, H_v=Y, and
(i) fails since W cannot be outside H_v₁. An empty intersection cannot supply W. An empty
base locus has no components, making (ii) vacuous as required. A nonreduced Y is allowed:
there is no IsReduced or IsIntegral hypothesis. Finite k is allowed: a nonempty open need
not contain a k-rational point, and the conclusion quantifies over all extension fields.
No injectivity or generation hypothesis on ψ and no separability hypothesis is imposed.
The auxiliary definition uses a finite sum, so its zero-dimensional case is also real data.

Searches made (all via the prescribed wrapper unless stated):

- LeanFinder: "General member of a linear system geometrically irreducible Bertini
  codimension two base locus"; eight generic irreducibility/rational-map results, no match.
- Loogle: `"GeometricallyIrreducible"`; twelve results giving the geometric irreducibility
  class and its base-change/fibre lemmas, no Bertini theorem.
- LeanSearch: "General member linear system geometrically irreducible Bertini"; eight
  hits on irreducible sets and geometrically reduced algebras, no match.
- Mathlib grep: `Bertini|bertini|codimension` in AlgebraicGeometry; three unrelated
  order-of-vanishing/algebraic-cycle comments, no matching theorem.
- Direct rg in WeilConjectures, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  `Bertini|bertini`: the existing Bertini finite-cover curve theorem is a different result;
  the Bertini–Noether polynomial theorem and generic irreducibility ring lemmas are also
  different. The source's RealSheaves module only uses the finite-cover theorem.
- `grep -rn lem-zl-bertini-irreducible-member WeilConjectures` found no occurrence.
- Direct rg for `linearSystemMemberIdeal|exists_open_geometricallyIrreducible_linearSystemMember`
  across both source libraries and the name index found no declaration-name collision.
- Searched existing linear-system, section, pullback, and codimension interfaces, and read
  `Order.coheight`, `IrreducibleCloseds`, `Hom.zeroLocus`, `homOfGlobalSection`, and the
  normalized tensor unit rather than introducing copies of these notions.

Validation: `scompile.py Q08 lem-zl-bertini-irreducible-member <module>` passed both sandbox
and library-path single-file compiles, cleanly, with no unexpected warnings. All universes
and variables are explicitly bound; every line is at most 100 characters.

## Second reading by Q08

This is the author's required second reading, not an independent reviewer claim; the
maintainer supplies the independent review under the dispatcher brief. I reopened the node
and the final Lean file and matched each of the clauses listed above. The base-locus
condition uses maximal components, not every subvariety; coheight has the correct direction;
all extension fields and all coefficient tuples are retained. The use of arbitrary basis
coordinates is invariant under GL_r(k). The helper uses the normalized canonical unit, not
an arbitrary map or a choice of unrelated sections. Both Y and its members may be
nonreduced. The structure morphism in the geometric-irreducibility conclusion is to Spec K.
The compiler exposed two type-elaboration issues in the first draft (global-section type
under pushforward and the coefficient ring for aeval); explicit `@id` and `(R := k)` repaired
them without changing any mathematical condition. No statement mismatch remains.
