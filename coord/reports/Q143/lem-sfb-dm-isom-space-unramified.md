## Worker report

The module `Sheaf.AlgebraicGeometry.DMIsomSpaceUnramified` states
`CategoryTheory.dm_isom_space_unramified`, with its proof wholly `sorry`.
It states the original node without changing any mathematical or dependency field.
No definitions, auxiliary theorems, or new nodes are needed.

Hypothesis and conclusion correspondence:

- The base scheme is `S : Scheme.{u}`. An arbitrary scheme over it is
  `T : Over S`, whose underlying scheme is `T.left`.
- The stack is `F : BasedCategory.{v, w} (Over S)`, with the exact recorded
  `hF : IsDeligneMumfordModuliStack F`. This includes the etale stack condition,
  algebraic-space diagonal, and representable surjective etale scheme atlas.
  No smoothness, separation, finite-type, or reducedness hypothesis is added.
- The objects are `x y : Functor.Fiber F.p T`, using the actual fibre category.
- The algebraic space over T is encoded as `I : AlgebraicSpace S` together with
  `p : I.obj.obj ⟶ yoneda.obj T`. This is the relative-space convention used by
  the dependency's `HasSpaceBaseChange`, `SpaceMapIsEtale`, and diagonal interfaces.
  For a scheme `U` over S and `q : U ⟶ T`, its points over q are exactly
  `{z : I.obj.obj.obj (op U) // p.app (op U) z = q}`. This encodes every T-scheme;
  specifying U over S with q over S is precisely specifying its map to T.
- The pullbacks `q*x,q*y` are any `xU yU : Functor.Fiber F.p U` with arrows
  `a : xU.val ⟶ x.val`, `b : yU.val ⟶ y.val` satisfying
  `F.p.IsHomLift q a` and `F.p.IsHomLift q b`. Such arrows exist and every one
  is strongly cartesian by the `IsFibredInGroupoids` clause of hF. Thus this
  quantification neither adds a hypothesis nor makes the Isom clause vacuous.
- The family `e` is an equivalence from the actual relative points to `xU ≅ yU`.
  These are isomorphisms in the fibre, so their arrows lie over the identity of U.
  In particular the statement retains the set of isomorphisms, not merely its
  nonemptiness, cardinality, or the set of isomorphism classes of objects.
- The entire final universal clause is naturality. For `f : U' ⟶ U`, arrows c,d
  between the pullbacks, lying over f and satisfying `c ≫ a = a'`, `d ≫ b = b'`,
  give the comparison with pullbacks along `f ≫ q`. For relative points z,z'
  with `z'.val = I.obj.obj.map f.op z.val`, the equation
  `(e ... z').hom.val ≫ d = c ≫ (e ... z).hom.val`
  says precisely that the isomorphism at z' is the pullback of the one at z.
  The cartesian universal property makes that restricted isomorphism unique.
  The identity-f case also enforces compatibility between any two choices of
  pullback lifts. This is a natural representation of the functor in the node,
  rather than unrelated pointwise bijections. No cleavage is an extra input.
- Unramifiedness is the first conjunct: every `V : Over S` and representable etale
  `b : yoneda.obj V ⟶ I.obj.obj` satisfies
  `IsUnramified ((yoneda.preimage (b ≫ p)).left)`. Yoneda extracts exactly
  the scheme composite V → I → T. `IsUnramified` is the recorded conjunction
  of locally finite type and open-immersion diagonal. Neither surjectivity
  nor affineness is required of a chart, so this covers every chart in the node.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsFibredInGroupoids`, `IsModuliStack`,
  `HasSpaceBaseChange`, `HasAlgebraicSpaceDiagonal`, `SpaceMapIsEtale`,
  `SpaceMapIsSurjective`, and `IsDeligneMumfordModuliStack` (the latter is the
  hypothesis; the others were opened to verify its complete meaning).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`
  and `AlgebraicGeometry.AlgebraicSpace.IsEtale`.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: `AlgebraicGeometry.IsUnramified`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`,
  the underlying scheme property used by `AlgebraicSpace.IsEtale`. The old node
  record calls it Etale, as the current source does; no deprecated alias is used.
- Proof imports: `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`,
  `AlgebraicGeometry.smooth_and_fibre_dimension_zero_of_etale`, and
  `Sheaf.AlgebraicGeometry.UnramifiedDiagonalEtaleAtlas`,
  `CategoryTheory.unramifiedModuliDiagonal_iff_etaleAtlas`.
  All stated proof dependencies' modules are imported. The four-step proof plan
  is reproduced in the theorem docstring.
- Mathlib's `Functor.Fiber`, its category instance and `fiberInclusion`, and
  `Functor.IsHomLift` provide fibre objects, fibre isomorphisms, and base-arrow
  conditions; they were read in Fiber.lean and the dependency interface.

Sources opened locally: stacks-morphisms.tex at `theorem-DM` (06N3) and
`lemma-properties-covering-imply-diagonal` (06MB), algebraic.tex at
`lemma-representable-diagonal` (045G), and stacks.tex at
`lemma-isom-as-2-fibre-product` (04SI). The latter gives the exact triple-to-Isom
identification and its pullback interpretation. The base-change reference 03ZJ
was located at `lemma-base-change-unramified` in spaces-morphisms.tex.

Edge cases checked mathematically before writing: the empty scheme is allowed
both as T and as any U, and the bijections still encode the unique empty-base
isomorphism; empty Isom sets give empty fibres of I, not assumed nonempty ones.
For a scheme stack the result is its usual relative Isom subfunctor. For BG with
G finite etale it gives the usual unramified Isom torsors; BG_m and Bμ_p in
characteristic p are not incorrectly included because the DM hypothesis excludes
those ramified stabilizers. Nonreduced schemes are unrestricted. x=y is allowed
and gives the automorphism functor, needed by the direct consumer. There is no
restriction on characteristic. Test schemes and S have the same universe u,
while the total category's object and arrow universes w,v are independent.

Searches (all on 2026-10-22):

- `msearch.py ... leanfinder "For a Deligne Mumford stack the isomorphism functor
  of two objects is represented by an unramified algebraic space"`: 8 hits,
  including scheme/algebra unramified predicates and stability instances,
  `AlgebraicGeometry.isomorphisms_eq_stalkwise` and `Scheme.Etale`; none states
  the stack Isom representability or its unramifiedness.
- `msearch.py ... leansearch "The isomorphism functor of two objects of a Deligne
  Mumford stack over a scheme is represented by an unramified algebraic space"`:
  8 hits, including `Algebra.FormallyUnramified.iff_of_equiv`,
  `AlgebraicGeometry.FormallyUnramified`, `CategoryTheory.Functor.mapIso`, and
  `Functor.relativelyRepresentable.of_isIso`; no stack result.
- `msearch.py ... loogle "AlgebraicGeometry.FormallyUnramified, CategoryTheory.Fiber"`:
  0 hits; Loogle reported unknown identifier `CategoryTheory.Fiber`. Source inspection
  then found the actual `CategoryTheory.Functor.Fiber` and its full interface.
- `msearch.py ... grep "DeligneMumford|deligneMumford|isomPresheaf|IsomSpace"`:
  0 hits in Mathlib. Direct rg for `dm_isom_space_unramified|isom_space_unramified`
  in Mathlib, `dag/lean_names_upstream.json`, `lean/WeilConjectures`, and `lean/Sheaf`:
  no existing declaration. Direct rg for the item id in `lean/WeilConjectures`:
  no hits. Searches for the DM and Isom/unramified vocabulary in `lean/Sheaf`
  found the recorded definition, atlas equivalence, and geometric-inertia consumer;
  the latter only mentions this item in its proof docstring. The broader fibre/pullback
  searches found Mathlib's existing lift interface, which is reused above.

The prescribed scompile.py compiled the delivered file successfully in both sandbox
and library contexts, with no errors or non-sorry warnings. No statement fault or
STATEMENT-DISPUTED condition was found. The CompactObject example module is currently
withdrawn (no declarations); the current recorded dependency modules supply the
same module/import/public-section header convention used here.

## Second reading by Q143

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
