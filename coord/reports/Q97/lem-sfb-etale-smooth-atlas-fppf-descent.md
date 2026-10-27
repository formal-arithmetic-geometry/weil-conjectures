## Worker report

Module: `Sheaf.AlgebraicGeometry.EtaleSmoothAtlasFppfDescent`.
Declaration: `CategoryTheory.isFppfModuliStack_of_etale_smooth_atlas`.
This is a statement-only delivery: its only theorem has proof `by sorry`.
Source read: `literature/stacks-project/criteria.tex`, the entire statement and proof
of Tag 076V, `lemma-stacks-etale`. Its opening proof paragraph explicitly says the
only new assertion is fppf stack descent: the diagonal and specified atlas are
independent of topology. The seven-step DAG proof is included in the docstring.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; the category of S-schemes is `Over S`.
  All universes `u v w` are explicitly declared. `Scheme.{u}` has object universe
  `u+1` and morphism universe `u`; total-category object and morphism universes
  `w v` remain unrestricted, including the larger universe of the size convention.
- The category fibred in groupoids is `F : BasedCategory.{v, w} (Over S)` with
  `hstack : IsModuliStack F`. Unfolding `IsModuliStack` includes
  `IsFibredInGroupoids F`, namely actual cartesian lifts and every arrow strongly
  cartesian. This gives groupoid fibres, retaining nontrivial automorphisms.
- The étale sheaf condition for isomorphisms and effectiveness for object descent
  are the rest of `IsModuliStack`: for every covering sieve of
  `Scheme.etaleTopology.over S`, a descent section has a colimiting cocone over T.
  The cocone gives the global object and its cartesian identification with the
  section; its universal property gives unique gluing of isomorphisms. This is
  exactly the existing project's total-category descent encoding.
- The algebraic-space diagonal is `hdiag : HasAlgebraicSpaceDiagonal F`.
  Its scheme-test 2-fibre products are represented by the existing
  `AlgebraicGeometry.AlgebraicSpace S`. In particular restricting both maps to
  the same T gives precisely the relative isomorphism space in the node.
  Conversely those isomorphism spaces give the general pair-of-schemes test
  after their scheme fibre product over S. No separatedness is imposed.
- The specified atlas scheme is `U : Over S`, and the morphism induced by its
  object x is `a : BasedFunctor (discreteModuli (yoneda.obj U)) F`.
  This is the standard fibred Yoneda presentation of x: evaluate at the identity
  of U to recover x; its values on maps T → U are cartesian pullbacks of x.
  Every base-preserving functor between these fibred groupoids preserves
  cartesian arrows. Thus this notation does not add an arbitrary map unrelated
  to x, or require a strict choice of cleavage.
- `hatlas : IsSmoothModuliAtlas F U a` quantifies over every test T and every
  object of F(T), expressed by its fibred Yoneda map. It asserts an actual
  algebraic space Z and its projection to T, with `HasSpaceBaseChange` giving
  an equivalence to the 2-fibre product compatible with this projection.
  `SpaceMapIsSmooth` tests smoothness on every representable étale scheme
  chart, using the recorded `AlgebraicGeometry.Smooth`.
  `SpaceMapIsSurjective` says each point of T lifts to a point of such a chart.
  This is equivalent to surjectivity on field-valued point classes: a lift to
  an algebraic space lifts to an étale chart after a field extension, and a
  chart lift maps to its class in the algebraic space. There is no requirement
  of surjectivity on rational points over the original field.
- The conclusion `IsFppfModuliStack F` uses the identical total category and
  descent encoding with `Scheme.fppfTopology.over S` instead of the étale
  topology. It expresses both fppf isomorphism sheaves and effective fppf
  descent. Together with the input `hdiag` and `hatlas`, it is precisely the
  node's final algebraic-stack assertion with the same U and the same a.
  Repeating those two hypotheses as tautological conclusion conjuncts would
  add no assertion and is intentionally avoided.

Dependency declarations read in full and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`,
  `Scheme.fppfTopology`; the slice is Mathlib's topology `.over S`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsAlgebraicSpace`, `IsRepresentableWith`, `IsEtale`, `IsSurjective`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme`. This is the recorded dependency for pointwise
  surjectivity and 2-base-change conventions, imported publicly.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsFibredInGroupoids`, `IsModuliStack`, `discreteModuli`,
  `moduliTwoFiberProduct`, `HasSpaceBaseChange`, `HasAlgebraicSpaceDiagonal`,
  `SpaceMapIsSurjective` (and the underlying `ModuliTwoIso`).
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `SpaceMapIsSmooth`,
  `IsSmoothModuliAtlas`, `IsAlgebraicModuliStack`.
- `Sheaf.CategoryTheory.SiteStackification`: `IsFppfModuliStack`.
- Proof-only import: `Mathlib.AlgebraicGeometry.Morphisms.Etale`, the recorded
  module of `def-weil-etale-morphism`. The original algebraic-space and fppf-site
  proof dependencies are already public statement imports. The four general
  supporting theorem nodes currently have no Lean record; no nonexistent module
  was imported, and their natural-language uses remain in the seven-step proof.

The existing landed nodes `def-sfb-stable-pointed-moduli-groupoids`,
`def-sfb-algebraic-moduli-stack`, and `def-sfb-fppf-stackification` were added to
`stmt_deps` to cite their interfaces. No node statement, proof, or other metadata
changed; no new notion, definition node, or dependency replacement was needed.
The size-convention node is metatheoretic and supplies no declaration to import.

Edge cases checked before writing: empty base or test schemes; the empty covering
of an empty scheme (allowed by both topology predicates); no nonempty or finite
index requirement; empty U (then the atlas hypothesis forces the corresponding
empty-stack cases); nontrivial stabilisers (the total groupoids and 2-fibre products
retain their isomorphisms); arbitrary characteristic and arbitrary non-Noetherian
S; lifts requiring a field extension; arbitrary specified atlas rather than a
new chosen atlas. No dimension, finiteness, separatedness, or characteristic
hypothesis was introduced. The predicates in the assumptions are genuine
geometric/descent conditions, not conditions true of every F or every a.

Searches for an existing statement:

1. `msearch.py leanfinder`, query “An etale stack in groupoids with representable
   diagonal and smooth surjective atlas is an fppf stack”: eight hits concerning
   étale scheme morphisms and sites; no comparison theorem.
2. `msearch.py loogle`, query
   `CategoryTheory.Functor.IsStack, AlgebraicGeometry.Smooth`: zero hits;
   the service reports the first identifier unknown. The actual local descent
   API was inspected directly, rather than relying on that stale name.
3. `msearch.py grep`, query
   `etale.*[Ss]tack|[Ss]tack.*fppf|[Ss]moothAtlas`: zero Mathlib hits.
4. `msearch.py leansearch`, query “An etale stack in groupoids with algebraic
   space diagonal and smooth surjective atlas satisfies fppf descent”: eight
   hits on pseudofunctor descent equivalences and flat morphism descent;
   none is the comparison statement of this item.
5. Direct `rg` searches of `lean/WeilConjectures`, `lean/Sheaf`, and Mathlib's
   descent directory for `IsStack`, `IsModuliStack`, `IsFppfModuliStack`,
   `IsSmoothModuliAtlas`, `RepresentableDiagonal`, and étale/fppf stack patterns;
   `rg` of the exact item id in `lean/WeilConjectures`; and a name search in
   `dag/lean_names_upstream.json`. Found the reused definitions above and
   downstream docstring citations, but no existing theorem with this conclusion.
   The new declaration name has no existing occurrence.

Validation: `scompile.py Q97 lem-sfb-etale-smooth-atlas-fppf-descent <module>`
passed both the sandbox and library-name compiles (10.5 s and 4.4 s), with no
errors or warnings. All variables and universes are bound, and the signature
in the node is copied verbatim from the file. No statement dispute or node fault.

## Second reading by Q97

A separate pass in this worker session reread the original node, Tag 076V, the
module, and the full definitions used in the signature. No second agent was
started, following the dispatcher's explicit instruction.

Checked every binder against the original statement: S is unrestricted; F has
all cartesian lifts and groupoid fibres through hstack; both étale descent
conditions are included; hdiag represents the actual 2-fibre products, not a
condition on isomorphism classes; U and a retain the specified object/atlas;
hatlas includes the projection and tests every base change. Its surjectivity
allows extensions of residue fields, rather than imposing rational-point
surjectivity. The conclusion changes only the descent topology to fppf, with
the same F, U and a still in scope. Its final algebraic-stack clause is exactly
the conjunction of that new condition and the existing two geometric hypotheses.
No implicit extra fibredness hypothesis or hollow conjunct was added. The
seven-step proof still follows the accepted quotient-comparison route.

The original statement needs no correction. The only DAG change besides lean
is adding the three already-landed definition nodes that own the predicates.
No mismatch was found and no signature change was required after compilation.
