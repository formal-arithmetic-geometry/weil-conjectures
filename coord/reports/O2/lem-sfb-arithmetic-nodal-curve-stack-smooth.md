## Worker report

The module `Sheaf.AlgebraicGeometry.ArithmeticNodalCurveStackSmooth` states
`AlgebraicGeometry.arithmetic_nodal_curve_stack_smooth`, with proof `sorry`.
Its two fully constructed helpers are `ProperCurveModuli.nodalCategory`, the literal full
subcategory selected by the recorded nodal predicate, and
`ProperCurveFamily.IsSmoothAfterBaseChange`, smoothness on every representable etale chart
of the canonical presheaf pullback with its second projection. Neither helper chooses data
from an existence theorem. They package the objects already introduced by this item's statement.

Clause-by-clause correspondence:

- An arbitrary scheme S is `(S : Scheme.{u})`, with the explicitly declared universe u and
  `set_option autoImplicit false`. There is no field, Noetherian, characteristic, connectedness
  or genus assumption.
- The specified groupoid C_S is exactly `ProperCurveModuli.category S`, using its original
  `ProperCurveFamily`, algebraic-space sources, flat/proper/finite-presentation properties,
  dimension-at-most-one geometric fibres, and cartesian arrows. These are not reconstructed.
- N_S is `ProperCurveModuli.nodalCategory S`: `fullModuliSubcategory` of that category with
  object predicate `fun X ↦ X.family.HasNonemptyNodalGeometricFibres`. The dependency checks
  nonemptiness of the actual geometric fibre and purity/nodes on every etale scheme chart.
- Algebraicity of C_S is the first conjunct `IsAlgebraicModuliStack (ProperCurveModuli.category S)`.
- Openness of N_S is the existential `N : OpenModuliSubstack ...` whose `property` equals that
  exact nodal predicate. `OpenModuliSubstack.open_pullback` includes an actual open immersion
  representing every scheme 2-base change and the isomorphism identifying its projection.
- Algebraicity and smoothness of N_S are the next two conjuncts, using the recorded
  `IsAlgebraicModuliStack` and `IsSmoothModuliStack` predicates on `nodalCategory S`.
- The equivalent smooth-chart criterion is an explicit iff. Every `W : Over S` and based
  functor from `discreteModuli (yoneda.obj W)` is tested. For every scheme base change it must
  have a space presentation `HasSpaceBaseChange p T t Z a` with `SpaceMapIsSmooth Z T a`.
  The conclusion is `Smooth W.hom`. There is no `SpaceMapIsSurjective` premise.
- The full smooth-family subcategory is explicitly an `OpenModuliSubstack` of the nodal
  category. Its object predicate is `AlgebraicSpace.MapToSchemeIsLocally (@Smooth)` on the
  original space and original structural map. Thus this clause uses the dependency's actual
  chartwise definition, not a free predicate.
- For each base `T`, family `X`, and hypothesis `X.HasNonemptyNodalGeometricFibres`, the
  theorem supplies `U : T.left.Opens`. For every `a : T' ⟶ T`, its canonical pullback is smooth
  exactly when there is `b : T'.left ⟶ U.toScheme` with `b ≫ U.ι = a.left`.
- Arbitrary-base-change compatibility is explicit: for every `a` the open `V` equals
  `a.left ⁻¹ᵁ U`, and every subsequent `b : T'' ⟶ T'` satisfies the same smoothness/factorization
  equivalence, using the actual composite `b ≫ a`. Both identity base changes are included.
- Scheme and sheaf fibre products are the existing `CategoryTheory.Limits.pullback`, with
  `pullback.snd` for the family projection. Open subschemes use `Scheme.Opens.toScheme`, `U.ι`
  and Mathlib `IsOpenImmersion`; scheme smoothness is Mathlib `Smooth`.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `ProperCurveFamily`, `ProperCurveModuli`,
  `ProperCurveModuli.category`, `AlgebraicSpace.MapToSchemeIsLocally` (with all family properties
  retained by the existing structure).
- `Sheaf.AlgebraicGeometry.CurveModuliGroupoids`:
  `ProperCurveFamily.HasNonemptyNodalGeometricFibres`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack`,
  `IsSmoothModuliStack`, `SpaceMapIsSmooth`; also its existing
  `StablePointedModuliGroupoids` interfaces `BasedFunctor`, `discreteModuli`,
  `HasSpaceBaseChange`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, `pullback.snd`.
- Added the already landed definition node `def-sfb-open-moduli-substack` to `stmt_deps`:
  `Sheaf.AlgebraicGeometry.OpenModuliSubstack`, `fullModuliSubcategory`, `OpenModuliSubstack`.
  This is an existing-node dependency addition authorized by the standing brief §5; no new
  node or dependency repair was needed.

Every proof dependency with a recorded module at writing time is imported privately, except
statement dependencies which are public. The universe-size convention is metatheoretic and
has no module. `lem-sfb-curve-formal-effectivity` and `lem-sfb-flat-space-smooth-locus` have no
recorded Lean module, so their proof imports are omitted. No statement needs those missing
proof statements. The locally-Noetherian Mathlib proof dependency is imported as
`Mathlib.AlgebraicGeometry.Noetherian`. The theorem docstring contains all ten DAG proof steps,
including their dependency ids.

Source check: opened the local Stacks text of quot.tex theorem-curves-algebraic (0D5A),
moduli-curves.tex lemma-nodal-curves (0DSY), lemma-nodal-curves-smooth (0E00),
lemma-big-smooth-part-curves (0DZX), lemma-smooth-curves (0DZZ), and stacks-morphisms.tex
lemma-local-source-target (06FM), definition-smooth (075U), lemma-base-change-smooth (075W).
The node's source.place still calls 0E86 the smooth-family openness lemma and lists 075V for
base change. The correct places, already identified in its review note, are 0DZZ and 075W;
the module cites these and no mathematical statement correction is needed. The nonempty
refinement of the usual nodal stack uses the open-and-closed nonempty-fibre locus as in DAG
proof step 5.

Edge cases checked against the source and signatures: empty S and empty test schemes;
nonempty nodal fibres impose no condition at absent geometric points; a family with an empty
geometric fibre is excluded from N_S but allowed in C_S; empty etale charts are allowed;
smooth, singular, disconnected and genus-zero nodal curves; all characteristics;
nonreduced and non-Noetherian bases; arbitrary, identity, open and nonsurjective base maps.
The smooth-family locus may be empty or the whole base. No surjectivity is imposed on W → N_S.
All schemes, presheaf values and geometric test fields use the existing scheme universe u.

Searches made (2026-10-24):

- `msearch.py ... leanfinder "The moduli stack of proper flat finitely presented nodal curve
  families is algebraic and smooth over any scheme"`: eight hits, only scheme smoothness,
  composition and relative-dimension declarations; no stack theorem.
- `msearch.py ... leansearch "Open substack of nonempty nodal proper curves is smooth over an
  arbitrary scheme"`: eight hits on scheme smoothness, open immersions, proper restrictions
  and ring smooth loci; no curve-moduli theorem.
- `msearch.py ... loogle "CategoryTheory.IsAlgebraicModuliStack,
  CategoryTheory.IsSmoothModuliStack"`: zero hits, unknown project identifier in the service.
- `msearch.py ... grep "NodalCurveModuli|nodalModuli|IsOpenModuli|IsSmoothModuli"`: zero Mathlib hits.
- `msearch.py ... grep "CurveStack|ProperCurveFamily|OpenModuliSubstack" AlgebraicGeometry`:
  zero Mathlib hits.
- `rg` of `lean/WeilConjectures` for the item id, nodal moduli names, fullModuliSubcategory,
  OpenModuliSubstack and the proposed names: no matching upstream theorem or helper.
- `rg` of `lean/Sheaf` found `NodalCurveStackSmooth.nodal_curve_stack_smooth`, which only
  concerns Spec of a field and field extensions; it lacks arbitrary S, the chart equivalence
  and the smooth-family open. Thus it is not an exact existing match. The same searches found
  the usable landed `OpenModuliSubstack` interface and `StackSmoothAtlasBaseChange` theorem.
  No declaration matches `arithmetic_nodal_curve_stack_smooth`, `nodalCategory` or
  `IsSmoothAfterBaseChange` in the sources read.
- Read all statement dependencies' JSON records and full source signatures/docstrings.
  There is no repair note for this item.

Validation: prescribed `scompile.py O2 lem-sfb-arithmetic-nodal-curve-stack-smooth` compiled
both sandbox and final module modes cleanly. An initial docstring ending warning was fixed;
the final run had no errors or warnings. No global build or direct git command was run.
No disputed statement or mathematical node fault remains.

## Second reading by O2

This dispatcher task explicitly forbids starting another agent, so this is a second pass by
the same worker, not an independent-review claim. The maintainer's independent review remains
the delivery review specified in the brief.

With the node and final file open, I checked all seven main clauses in order: arbitrary S;
C_S algebraic; the identical nodal predicate defines a full open; that exact full category is
algebraic and smooth; the iff tests all smooth representable maps without surjectivity;
the smooth families form a full open using the original structural projection; and the
smooth-family open has the all-base-change factorization criterion and inverse-image law.
The helper's `pullback.snd` is essential: it maps to the new test base, not the old curve.
The inverse-image clause tests `b ≫ a` and factors `b.left`, so it characterizes the smooth
locus after the specified first base change. Original and pulled-back identity cases are
included. The equality of the open predicate with chartwise smoothness avoids replacing
smooth families by an arbitrary open. All type/universe binders are explicit. No changed
hypothesis or conclusion was found. The only correction during compilation was formatting
the theorem docstring ending; the node's statement, proof and proof_deps remain unchanged.
