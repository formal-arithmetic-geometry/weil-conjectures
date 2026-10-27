## Worker report

The module `Sheaf.TraceFormula.FiniteSmoothCurveFamilyEuler` states
`AlgebraicGeometry.Scheme.Modules.finite_smooth_curve_family_euler`, with its sole proof
`sorry`. It also constructs the canonical restriction map and its components, with real
data and no postponed proof. No node statement, dependency list, or proof plan is changed.

Source read: Stacks `coherent.tex`, `lemma-relative-affine-cohomology` (Tag 089W);
`varieties.tex`, `lemma-euler-characteristic-additive` (Tag 08AA); `curves.tex`,
`definition-genus` (Tag 0BY7), including the surrounding arithmetic-genus discussion.
The current latest blueprint locality node is about contracting correspondences; as the
accepted split report already explains, this is the historical coherent-curve tool below
its Appendix B normalization calculation, not a change to that current unit statement.
The item and every statement dependency's statement and Lean/mathlib binding were read.
The old Sheaf CompactObject example is withdrawn, so I also read the recorded upstream
`WeilConjectures.CategoryTheory.CompactObject` declaration and its source/docstring.

Hypothesis and clause correspondence:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- A proper k-scheme is `(X : Scheme.{u}) [X.Over (Spec (.of k))]` and
  `[IsProper (X ↘ Spec (.of k))]`.
- The finite set is `(I : Type v) [Fintype I]`. The index universe is independent of
  the scheme universe; finite types automatically have the required smallness.
- The family is `(C : I → Scheme.{u})`, with an `Over` instance for every member.
  `IsConnectedCurve` includes nonemptiness, connectedness, dimension exactly one,
  separatedness and finite type. The separate `Smooth` and `IsProper` instances
  impose exactly smoothness and properness over k.
- The maps are `(h : ∀ i, C i ⟶ X)` with `IsFinite (h i)` and
  `(h i).IsOver (Spec (.of k))`. Thus each is a finite k-morphism, including the
  required equality of its composite structure map with that of C_i.
- The coproduct C is `∐ C`; the morphism h is `Sigma.desc h`, whose composite with
  each `Sigma.ι C i` is `h i`. No unrelated morphism is chosen.
- G_i is `(pushforward (h i)).obj (unit (C i))`; B is
  `(pushforward (Sigma.desc h)).obj (unit (∐ C))`. `pushforward_obj_obj` in Mathlib
  makes the required sections description definitionally exact.
- The first two conjuncts assert `RingedSpace.IsCoherent` for every G_i and for B.
  This is the finite-type plus finite-type-kernel predicate, not merely the
  quasi-coherent/finite-type conjunction also exposed by the dependency module.
- `finiteCurveFamilyRestrictionComponent` first applies the scheme structure map
  of the coproduct inclusion, expressed as `unitToPushforwardObjUnit`, and pushes
  it forward along `Sigma.desc h`. `pushforwardComp` and `pushforwardCongr` along
  `Sigma.ι_desc` identify the target with G_i. All these maps have their genuine
  section restriction/structure-map data. `finiteCurveFamilyRestriction` is their
  `Pi.lift`. The third conjunct says this specific map is an isomorphism B to the
  categorical product. The following `Nonempty (product ≅ coproduct)` expresses
  that this finite product is also the direct sum, both in X.Modules. This does
  not replace the canonical restriction by an arbitrary isomorphism.
- For every i and every natural degree q, the next conjunct supplies a k-module
  isomorphism e whose underlying additive map is exactly
  `moduleCohomologyEdgeMap (h i) (unit (C i)) q`. The latter is definitionally
  `moduleCohomologyFMap` of the identity on G_i. Its source and target are precisely
  the recorded `RingedSpace.moduleCohomology` objects, restricted along
  `Scheme.globalSectionsRingHom k` on X and C_i respectively. Thus no unrelated
  cohomology isomorphism or unspecified scalar action substitutes for the edge.
- Degree zero supplies a k-linear equivalence from k to the module-resolution
  cohomology, together with its value on every a: the structure ring map followed
  by `globalSectionsFunctor.toRightDerivedZero.app`. This specifies the actual
  structure map into H^0, rather than only asserting dimension one or an abstract
  equivalence. Its underlying algebra structure is the usual one via the canonical
  degree-zero/global-sections identification; bijectivity is the asserted isomorphism.
- `∀ q, 1 < q → Subsingleton (...)` asserts zero cohomology in all degrees above one.
- The existing `Hom.genus` uses differential forms; the next equality explicitly
  identifies it with `Module.finrank k` of the recorded module-resolution H^1.
  This renders the node's g_i = dim H^1 while retaining the unique existing genus.
- The subsequent equalities give chi(X,G_i) = chi(C_i,O_Ci) and
  chi(C_i,O_Ci) = 1 - g_i. The Euler characteristic is the recorded
  `Scheme.Modules.eulerChar`; no new Euler invariant is defined. Its Ext-based
  cohomology and the module-resolution cohomology agree by the standard comparison;
  this comparison is proof work, not an extra assumption.
- The total formula is `eulerChar k B = (Fintype.card I : ℤ) - ∑ i, (genus_i : ℤ)`.
  The final implication from `IsEmpty I` gives both `IsZero B` and chi(X,B)=0.
- X has no connectedness, reducedness, dimension, component-embedding, or
  birationality assumption; none is hidden in the helper definitions.

Statement dependency declarations used (all source signatures and docstrings inspected):

- `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`:
  `Scheme.Modules.eulerChar`, `Scheme.globalSectionsRingHom`.
- `WeilConjectures.AlgebraicGeometry.Curve`: `IsCurve`, `IsConnectedCurve`,
  `Scheme.Hom.genus`.
- `WeilConjectures.Topology.RingedSpaceModuleCohomology`:
  `RingedSpace.moduleCohomology`, `RingedSpace.globalSectionsFunctor`.
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap`:
  `Scheme.Modules.moduleCohomologyFMap`, `Scheme.Modules.moduleCohomologyEdgeMap`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; `Field` is Mathlib's
  field structure. AlgebraicClosure is not needed to select a closure here.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`.
- `Sheaf.CategoryTheory.RingedSiteModules` exposes the exact Mathlib
  `SheafOfModules` category. `Scheme.Modules`, `unit`, `pushforward`,
  `pushforwardComp`, and `pushforwardCongr` are the scheme specialization in
  `Mathlib.AlgebraicGeometry.Modules.Sheaf`; `unitToPushforwardObjUnit` is Mathlib's
  canonical structure-module morphism.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` publicly exposes the exact
  `WeilConjectures.AlgebraicGeometry.Coherent` declaration `RingedSpace.IsCoherent`.

The stated proof dependencies are imported with plain imports: invertible modules;
coherent finite pushforward, kernel/cokernel/sums, and coherence finite-type criterion;
affine cohomology edge; global functions; cohomological dimension bound; finiteness
of proper coherent cohomology; Euler additivity. The one proof dependency
`lem-trf-proper-field-invertible-coherent` currently has no Lean record and hence no
module to import. It is not needed to type the statement and is not duplicated here.
Every one of the node's six proof steps is reproduced in the theorem docstring.

Edge cases checked before writing and on rereading:

- I empty: no nonempty instance is required for I; the coproduct is the empty
  scheme; its direct-image structure module is zero. The final two conclusions
  and the total Euler formula give zero, including when X itself is empty.
- I singleton and h an identity on a curve: restriction has one coordinate,
  the edge map is the identity comparison, and chi=1-g.
- P^1 has g=0 and chi=1; a genus-one smooth proper connected curve has chi=0.
- Repeated curves with the same finite map, and a finite map of degree greater
  than one: there is no embedding or birationality assumption and no erroneous
  degree factor in the Euler characteristic.
- A curve mapped into a higher-dimensional proper X, or a proper nonreduced X:
  none of the target geometry is restricted to a reduced curve.
- q=0 is included in the canonical edge assertion; q=1 is excluded from the
  higher vanishing assertion; q>1 gives zero. All field characteristics remain.

Searches actually run (Q155 wrapper search log):

- LeanFinder: "The Euler characteristic of a finite pushforward from a finite
  disjoint union of smooth proper connected curves equals the number of curves
  minus the sum of their genera". Eight hits: extensive/disjoint coproduct
  infrastructure, finite coprod maps, a Galois cardinality identity, and incidence
  algebra Euler characteristic. None states this coherent-cohomology theorem.
- Loogle: `AlgebraicGeometry.Scheme.Modules.eulerChar,
  AlgebraicGeometry.Scheme.Hom.genus`: no hit; service reported the first identifier
  unknown (the remote index does not contain the project). This was not treated as
  evidence of absence from the project.
- Loogle: `"IsFinite", "IsProper"`: six hits relating proper, affine, finite, and
  locally quasi-finite morphisms. None has the cohomology/family conclusions.
- Mathlib grep through msearch: `eulerChar|eulerCharacteristic|genus|affine.*cohomology`
  in AlgebraicGeometry: zero hits.
- LeanSearch: "Cohomology and Euler characteristic of finite pushforwards from smooth
  proper connected curves and finite coproducts": eight hits, providing finite
  coproducts, additive pushforward and its sections, properness of finite maps,
  and Galois finite-coproduct preservation; no matching theorem.
- `grep -rn` of the exact item ID in `lean/WeilConjectures`: no hit.
- `rg` of genus/Euler/cohomology keywords in both `lean/WeilConjectures` and
  `lean/Sheaf`: existing Euler additivity, affine Euler invariance, and
  normalization/genus consumers were found and inspected; none states this
  family theorem with its canonical edge, coherence, and empty-family clauses.
- `rg` for both new helper names and the new theorem name in both project roots
  and `dag/lean_names_upstream.json`: no existing declarations.

Validation: scompile.py compiled the file both in its sandbox import mode and
as `Sheaf.TraceFormula.FiniteSmoothCurveFamilyEuler`, cleanly (34.3 s and 7.2 s).
No extra definition nodes, dependency repairs, statement correction, or disputed
mathematical assertion are required.

## Second reading by Q155

A separate rereading pass was performed by this worker; no second agent was
started, as the dispatcher brief prohibits that. The maintainer's independent
review is still required and is not claimed here.

I reread the node beside the full theorem signature and the actual helper
bodies. All field, finite-family, curve, finite-map and k-morphism hypotheses
are present, and there is no extra condition on X. The component restriction
uses the actual coproduct inclusion and the equality `Sigma.ι_desc`, not an
unconstrained arrow. The edge clause compares the underlying map of the
k-module isomorphism with the exact recorded identity-h-map edge. Both the
zero-degree map's value on scalars and the genus identification with H^1 are
explicit, preventing abstract equivalences from silently replacing those maps.
The three Euler equalities and both empty-family assertions are present.
I checked every helper for postponed data and every binder for auto-implicits;
both autoImplicit options are false. No mismatch was found and no correction
of the node was necessary. The old example's withdrawn status and the absent
proper-field proof import are documented rather than worked around.
