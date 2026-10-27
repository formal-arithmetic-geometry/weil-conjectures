## Worker report

Item: `def-sfb-affine-action-quotient-stack`, group Q109, stage 2.
Module: `Sheaf.AlgebraicGeometry.AffineActionQuotientStack`.
Main declaration: `AlgebraicGeometry.affineActionQuotientStack`.

The module specializes the already landed scheme-torsor total category to the
specified affine action. It adds the missing chosen pullbacks, pullback functor,
canonical map from the action scheme, and maps to algebraic spaces modulo vertical
natural isomorphism. Definitions have explicit data. Each postponed proof is a
named theorem for the structural laws of this definition, with the source and
complete proof plan in its docstring. No theorem about algebraicity or an atlas
being smooth/surjective is asserted. `quotientAtlas` is the conventional name for
the specified canonical functor, without asserting any atlas property.

Sources read: Stacks `examples-stacks.tex`, Situation 04WL, construction of
`[[X/G]]`, and Proposition 04WM; `spaces-groupoids.tex`, definition of torsors
(existence of a trivializing covering) and Tag 044Q. Also read the current
blueprint unit `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/_section.md`. The node is a supporting definition, not the
unit's statement. No correction of the statement was needed.

Clause-by-clause correspondence:

- The field is `(k : Type u) [Field k]`. The finitely generated commutative
  k-algebra is `(E : Type u) [CommRing E] [Algebra k E]
  [Algebra.FiniteType k E]`. This is exactly
  `RingHom.FiniteType (algebraMap k E)` by `RingHom.finiteType_algebraMap`, so it
  uses the recorded finite-type-algebra notion, with the algebra structure fixed.
- `affineActionScheme k E` is literally `Over.mk (Spec.map
  (CommRingCat.ofHom (algebraMap k E)))`, hence U = Spec E with its specified
  k-structure, rather than an arbitrary affine presentation.
- `G : Over (Spec (CommRingCat.of k))` with `[GrpObj G]` is a k-group scheme.
  `[Smooth G.hom]` is smoothness, `[IsAffineHom G.hom]` is affineness over the
  affine base, and `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]` is finite
  type in the dependency's recorded convention. There is no assumption on
  characteristic, reductivity, connectedness, or freeness of the action.
- `[ModObj G (affineActionScheme k E)]` consists of the actual morphism a
  and exactly its unit and associativity diagrams. Products in `Over S` are
  scheme fibre products over S. `MonObj` and `GrpObj` retain the multiplication,
  unit and inverse. The general helper section works over an arbitrary scheme S;
  the main declaration binds precisely the affine field-base hypotheses.
- The chosen big site has underlying category `Over (Spec (.of k))` and topology
  `Scheme.fppfTopology.over (Spec (.of k))`. It enters the construction through
  the reused `SchemeAction.IsLocallyTrivial`. Its covering sieve is existential,
  not universal. For each arrow in that sieve, the cartesian equivariant map
  `G ⊗ W → P` identifies its source with `P ×_T W`. The generated fppf topology
  makes this equivalent to the existence of the covering family in the node.
- `SchemeAction.TorsorObject G U` retains the base T, the scheme P, its action,
  invariant projection P → T, local triviality, and the map P → U. Its
  `equivariant` field tests the equality on every test scheme W, including the
  universal test object G × P, so it is precisely equality of morphisms, not
  equality merely on geometric points. An invariant G-action on P over T is
  equivalently a G_T-action; no choice of action is forgotten.
- `SchemeAction.TorsorHom X Y` retains the base arrow h and torsor map q.
  `cartesian : IsPullback q X.projection Y.projection h` is precisely that
  `(q,p') : P' → P ×_T T'` is an isomorphism. Its `equivariant` field is the
  required G-equivariance, and `commutes : q ≫ Y.map = X.map` is f' = f ∘ q.
  These are the existing definitions; they are not copied in this delivery.
- The existing category instance composes base maps and scheme maps, using
  `IsPullback.paste_horiz` for the composite square. Identity is the two identity
  maps. Its projection in `torsorGroupoid` sends X to X.base and r to r.base.
  Thus the main declaration retains exactly the projection requested by the node.
- `torsorFiber` is the ordinary fibre category `Functor.Fiber`, with arrows
  lifting the identity; it is not a set of isomorphism classes or a restricted
  core. `torsor_fiber_isGroupoid` states that all its arrows are invertible.
  The cartesian condition over an identity says exactly that the underlying
  torsor morphism is an equivariant isomorphism commuting with f.
- `torsorPullback X T' h` has space `pullback X.projection h`, projection
  `pullback.snd`, and map `pullback.fst ≫ X.map`. Its action is the explicit
  `pullback.lift` in `torsorPullbackActionMap`; its two projections are
  `(g,p,t') ↦ g • p` and `(g,p,t') ↦ t'`. The named laws provide only the proof
  fields for this actual map and the pulled-back local-triviality condition.
- `torsorPullbackArrow` has base exactly h and torsor map exactly
  `pullback.fst`, with the canonical pullback square. `torsorPullbackMap` is
  the explicit lift with projections `pullback.fst ≫ r.map` and `pullback.snd`.
  For a vertical arrow this is r ×_T id, as required. Its general form also
  permits the equality hY = hX ≫ r.base, without changing the map.
- `torsorPullbackFunctor` supplies the actual functor between ordinary fibres.
  Objects and arrows use the preceding maps. The equality transports merely
  identify the base of a fibre object with T; they introduce no additional
  choice. The named functor laws assert preservation of identities and composition.
- `schemeToActionGroupoid` sends a test map x to the action object (T,x),
  with label 1 on base arrows. Composing it with the existing
  `trivialTorsorFunctor` defines `quotientAtlas`. Objects are the actual trivial
  torsor with map (g,t) ↦ a(g,x(t)). The existing inverse-right-translation
  formula for arrows becomes (g,t') ↦ (g,h(t')) because the label is 1.
  Representable points are encoded by `discreteModuli (yoneda.obj U)`; Yoneda
  preimage gives the actual map x, without choosing a representative arbitrarily.
- An algebraic space is the recorded `AlgebraicSpace S`, whose underlying
  presheaf is `Z.obj.obj`. `discreteModuli Z.obj.obj` is its existing discrete
  fibred groupoid. Objects are maps h_T → Z (equivalently z ∈ Z(T)); a morphism
  over h is the commuting-triangle condition z' = z ∘ h, and has no extra data.
- `quotientSpaceMapSetoid` relates two `BasedFunctor`s to that discrete groupoid
  exactly when `Nonempty (F ≅ H)` in the category of based functors.
  Such isomorphisms are natural isomorphisms over the base, not arbitrary
  natural isomorphisms of underlying functors. `quotientSpaceMaps` is the
  quotient by this relation, exactly the maps specified in the final clause.

Dependency interfaces read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs (provided through imports).
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`,
  Mathlib.CategoryTheory.Monoidal.Grp; its specialization to `Over (Spec k)` was
  checked in WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType` and `QuasiCompact`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType and .QuasiCompact.
- `def-weil-affine-spectrum`: `Spec`, `Spec.map`,
  Mathlib.AlgebraicGeometry.Scheme.
- `def-pc-fppf-site`: `Scheme.fppfPrecoverage`, `Scheme.fppfTopology`,
  Mathlib.AlgebraicGeometry.Sites.Fpqc, and `GrothendieckTopology.over`,
  Mathlib.CategoryTheory.Sites.Over.
- `def-trf-algebraic-space`: `AlgebraicSpace`,
  Sheaf.AlgebraicGeometry.AlgebraicSpace, read through its sheaf, representable
  diagonal, and atlas definitions.
- `def-weil-pbc-finite-type-algebra`: `RingHom.FiniteType`,
  Mathlib.RingTheory.FiniteType, with its exact algebra-map equivalence.
- `def-weil-scheme-over-base`: `Scheme.Over`/`Hom.IsOver` and their bundled
  `CategoryTheory.Over` form, Mathlib.AlgebraicGeometry.Over.
- `def-pc-fibre-product`: `pullback`, its two projections, `pullback.lift` and
  `IsPullback`, Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback.
- Added the already landed `def-sfb-scheme-action-torsor-groupoids` to stmt_deps:
  Sheaf.AlgebraicGeometry.SchemeActionTorsorGroupoids, all torsor/action objects,
  arrows, local-triviality, total projections and trivialTorsorFunctor above.
  Its full statement and every used declaration were read.
- Added the already landed `def-sfb-stable-pointed-moduli-groupoids` to stmt_deps
  for the exact existing `CategoryTheory.discreteModuli`, in
  Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids. Only its general discrete
  fibred groupoid vocabulary is used, not a stable-curve hypothesis.
- The action structure is Mathlib's `ModObj` and its functor-of-points action,
  Mathlib.CategoryTheory.Monoidal.Mod and .Cartesian.Mod. No second action
  definition is introduced.

The only node fields changed are lean and the addition of these two already
landed statement dependencies. No dependency node is rewritten and no new node
is required. All new helpers belong to the existing owning definition's specified
pullback, groupoid and canonical-map operations. The nine postponed theorems are
`pullback_action_compatible`, `pullback_action_laws`, `pullback_object_laws`,
`pullback_projection_equivariant`, `pullback_map_compatible`, `pullback_map_laws`,
`torsor_fiber_isGroupoid`, `fiber_pullback_compatible`, and
`fiber_pullback_functor_laws`, all in `AlgebraicGeometry.SchemeAction`.
Their docstrings supply the natural-language proofs. No definition contains sorry.

Edge cases checked before and after writing:

- E can be the zero ring, so U can be empty; no Nontrivial E was imposed.
- T or T' can be empty. Local triviality is still an existential covering sieve;
  no nonempty indexing or nonempty-scheme restriction occurs.
- The trivial group gives the usual representable discrete groupoid; no orbit
  collapse is built into the definition.
- For U = Spec k, the torsor groupoid retains nontrivial torsors and their
  automorphisms (BG); local triviality does not force global triviality.
- Stabilizers are retained, and a noncommutative G is allowed. The canonical
  map uses left translation and label 1, consistent with the inverse-right-label
  convention of the existing trivial-torsor functor.
- Identity base maps and successive base changes use actual chosen pullbacks
  and their universal properties; no strict equality of iterated fibre products
  is assumed.
- The test-scheme universe is the same as Scheme.{u}, whose object type is
  Type (u+1) and morphisms are in Type u. No lower independent test universe
  or equality of the object and morphism universes is imposed.
- Empty Hom sets and arbitrary algebraic spaces are allowed. The quotient
  equivalence is vertical natural isomorphism, including its identity case.

Searches performed (using the required msearch.py wrapper):

1. LeanFinder, `quotient stack of a group scheme torsors equivariant morphism`:
   eight hits on type-action quotients, orbit/stabilizer constructions, and a
   locally ringed space coequalizer; no scheme-torsor quotient stack.
2. Loogle, `"Torsor", "Action"`: two type-torsor forgetful projections
   (`AddTorsor.toAddAction`, `Torsor.toMulAction`); no scheme construction.
3. Mathlib grep, `quotientStack|QuotientStack|Torsor|torsor`, CategoryTheory:
   zero hits. The actual internal group/action APIs were then read directly.
4. LeanSearch, `quotient stack of a group scheme acting on a scheme with objects
   equivariant torsors`: eight hits on orbit quotients, additive type torsors,
   representations and topological covering maps; no matching scheme quotient.
5. Project rg, `quotientStack|quotient_stack|QuotientStack|classifyingStack`,
   lean/WeilConjectures and lean/Sheaf: zero hits. The direct blueprint-id search
   in WeilConjectures likewise found no declaration.
6. Project rg for torsors/action groupoids found the landed
   SchemeActionTorsorGroupoids module. Its definitions were reused, including
   the canonical trivialTorsorFunctor; it lacks the chosen pullback and
   representable-to-torsor functor completed here.
7. Exact-name searches for `torsorFiber`, `torsorPullbackFunctor`,
   `affineActionQuotientStack`, `quotientAtlas`, `quotientSpaceMaps`, and
   `affineActionScheme` in WeilConjectures, Sheaf and dag/lean_names_upstream.json
   found no collisions.

No STATEMENT-DISPUTED flag. No hollow data or additional mathematical hypothesis.
Every compiler invocation used the prescribed scompile.py wrapper; no local/global
build or direct repository mutation was run. The final compile and delivery dry
run results are recorded below after validation.

## Second reading by Q109

The dispatcher expressly forbids starting other agents and assigns independent
review to the maintainer. This is a second self-reading, not a claim of an
independent review. The local source and node were reread together, especially
the existential covering, cartesian-arrow direction, identity-labelled atlas,
vertical natural-isomorphism quotient, and the ordinary fibre (rather than a
core). The initial compiler diagnostics in the representable functor's
composition and the explicit hom-lift proof were repaired without changing the
mathematical statement. Independent review remains with the maintainer.

Validation: the final scompile.py run passed both sandbox and library compilation
with no errors or warnings (49.1 s and 26.4 s, within the 60 s per-file limit).
The prescribed deliver2.py --no-push completed with
`OK (dry run): commit 69c3c11d377 passes the preflight and compiles; nothing pushed`.
