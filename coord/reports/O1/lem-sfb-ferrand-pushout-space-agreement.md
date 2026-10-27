## Worker report

This delivery states `AlgebraicGeometry.AlgebraicSpace.ferrand_pushout_space_agreement`
in `Sheaf.AlgebraicGeometry.FerrandPushoutSpaceAgreement`, with its sole proof `sorry`.
The natural-language statement and accepted stage-1 split are unchanged. There are no
new nodes, dependency repairs, extra assumptions, or data definitions.

The inherited BLOCKED ending concerned a stage-1 resplit. The live node is split and
reviewed PASS by Q01 on 2026-10-24 but has no Lean record. As coord/brief-stage2.md §0
explicitly directs, this stage-2 assignment records its statement rather than resplitting it.
No released repair note for this item was present.

Clause-by-clause correspondence:

- The base scheme is `(S : Scheme.{u})`; the four schemes over it are
  `(Z X T P : Over S)`. Their relative structure maps are retained by `Over S`.
- The diagram maps are `(i : Z ⟶ X)` and `(j : Z ⟶ T)`, so both commute with the
  structure maps to S.
- The closed-immersion hypothesis is `[IsClosedImmersion i.left]`.
- The integral-morphism hypothesis is `[IsIntegralHom j.left]`, with no finiteness
  or finite-presentation hypothesis.
- For every point of T the affine-neighbourhood hypothesis is
  `hAffine : ∀ t : T.left, ∃ U : X.left.Opens, IsAffineOpen U ∧
  ∀ z : Z.left, j.left z = t → i.left z ∈ U`.
  This is exactly containment of the image of the entire set-theoretic fibre in U.
- The given cocone maps are `(a : X ⟶ P)` and `(b : T ⟶ P)`. Its pushout in schemes,
  rather than only a relative pushout, is
  `hPushout : IsPushout i.left j.left a.left b.left`.
  Mathlib's `IsPushout` contains commutativity and `IsColimit` of its pushout cocone.
- Every target algebraic space over S is quantified by `(H : AlgebraicSpace S)`.
  The recorded definition is the full subcategory of fppf sheaves with representable
  diagonal and a surjective etale atlas; its morphisms are natural transformations.
- Maps from the schemes X and T to H are
  `f : yoneda.obj X ⟶ H.obj.obj` and `g : yoneda.obj T ⟶ H.obj.obj`.
  Here Yoneda is on `Over S`, so these are exactly morphisms over S from the
  represented schemes to the underlying sheaf of H. This is the definition of maps
  to an algebraic space, not an arbitrary substitute for the scheme embedding.
- The compatibility equation is `yoneda.map i ≫ f = yoneda.map j ≫ g`.
- The conclusion `∃! h : yoneda.obj P ⟶ H.obj.obj, ...` gives existence and uniqueness
  of the morphism over S. Its two required restrictions are the conjunction
  `yoneda.map a ≫ h = f ∧ yoneda.map b ≫ h = g`.

Dependency declarations used:

- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (their complete definitions and docstrings read).
- def-weil-closed-immersion: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion` (closed embedding and surjective stalk maps).
- def-weil-finite-integral-morphism: its recorded module
  `Mathlib.AlgebraicGeometry.Morphisms.Finite` publicly imports Integral, where
  `AlgebraicGeometry.IsIntegralHom` is affine with integral maps on affine sections.
- def-weil-pbc-category-colimit: `Mathlib.CategoryTheory.Limits.HasLimits`, and
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs` for `IsPushout`.
  Its `isColimit'` field uses the recorded `CategoryTheory.Limits.IsColimit` notion.
- def-trf-algebraic-space: `Sheaf.AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace` and `IsAlgebraicSpace`; read the full source
  through the defining sheaf category, representability, diagonal and atlas conditions.
- Proof-only import: `Sheaf.AlgebraicGeometry.FerrandSchemePushout`,
  `AlgebraicGeometry.exists_ferrand_scheme_pushout` (its full signature and proof
  docstring read). The other two proof dependencies,
  lem-sfb-ferrand-etale-scheme-patching and lem-sfb-scheme-colimit-upgrade-space-targets,
  have no Lean record; no unavailable proof module is imported. They are not needed
  to type the statement. The theorem docstring preserves all four accepted proof steps.

Source and edge cases:

Read `literature/stacks-project/spaces-pushouts.tex`,
`lemma-pushout-along-closed-immersion-and-integral` (0EDP), and
`literature/stacks-project/more-morphisms.tex`,
`situation-pushout-along-closed-immersion-and-integral`. The latter assumes exactly
closed immersion, integral map, and affine neighbourhoods of each fibre.

Checked: Z empty (the diagram reduces to a coproduct); X, T or P empty when the
morphisms permit it; i the identity (the pushout is T); j the identity (the pushout
is X); empty fibres (the universally quantified implication imposes no point in U,
and the empty affine open is allowed); nonempty fibres with multiple points
(the same U must contain all their images); arbitrary integral rather than finite j;
non-Noetherian schemes; arbitrary, potentially nonseparated algebraic-space targets;
and arbitrary universe u. No nonemptiness, separation, quasi-compactness, finite type,
or characteristic restriction is introduced. No statement dispute or node fault found.

Searches for existing statements (all on 2026-10-24):

- msearch.py leanfinder: "A scheme pushout along a closed immersion and an integral
  morphism is also a pushout in algebraic spaces". Eight hits: integral morphisms
  under coproduct/base change, open-immersion scheme gluing and Spec of ring pushouts;
  none is the desired algebraic-space-target universal property.
- msearch.py leansearch: "A Ferrand scheme pushout is also a pushout in algebraic
  spaces". Eight hits, concerning ring pushouts and contravariant Spec pullbacks;
  none matches.
- msearch.py loogle: `CategoryTheory.IsPushout`. Twelve hits give the general
  `IsPushout`/cocone/IsColimit API; none states the geometric comparison.
- msearch.py grep: `Ferrand|ferrand|pushout` in Mathlib/AlgebraicGeometry.
  Twenty-five hits concern scheme gluing, ring pushouts or fibre products, no match.
- rg on lean/WeilConjectures: `Ferrand|ferrand|pushout.*(space|Space)|(space|Space).*pushout`
  gives only topological compactness and tangent-space constructions; no match.
  The item's exact blueprint id has no hit there.
- rg on lean/Sheaf with the same expression finds FerrandSchemePushout (scheme
  targets only), SpaceAffineThickeningPushout (only thickenings), and users' proof
  docstrings. These do not state the arbitrary closed-integral comparison here.
  In particular a closed immersion need not be a thickening, so the latter theorem
  does not cover this node. The exact item id has no pre-existing declaration.

Validation: scompile.py compiled the delivered module in sandbox and library module
modes against the server's published build, cleanly (5.2 s and 6.0 s). Every universe
and variable is explicitly bound. There is one theorem, only a sorry proof, no extra
construction, no local notation/instance, and every source line has at most 100 characters.

## Second reading by O1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
