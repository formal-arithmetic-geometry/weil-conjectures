## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit` states
`AlgebraicGeometry.IsCurve.exists_kernel_cocone_isIso_colimitDesc_of_genericVanishing`.
Its only theorem has proof `sorry`; it introduces no definitions or instances.
The server single-file compile succeeded without warnings (3.8 seconds).

Hypothesis and clause correspondence:

- An algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- The integral curve over that field is `{C : Scheme.{u}}`, its structure morphism
  `f : C ⟶ Spec (.of k)`, `[IsCurve f]`, and `[IsIntegral C]`. `IsCurve`
  supplies separatedness, finite type, and dimension at most one; exact dimension
  one, smoothness, and properness are not imposed.
- The abelian sheaf is `G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}`.
- Nonempty affine opens are the source's `C.NonemptyAffineOpens`, whose underlying
  partial order is inclusion. The diagram domain `C.NonemptyAffineOpensᵒᵖ`
  reverses inclusion. The existing integrality-based instances make it filtered.
- The inclusions `j_U` are `C.affineOpensDiagramι.app U`. The source's
  `C.affineOpenUnit U G` is exactly the component at `G` of
  `Etale.upperStarLowerStarAdjunction AddCommGrpCat` for this inclusion.
  This inclusion uses the canonical affine spectrum presentation of the open,
  isomorphic to the open subscheme itself.
- `D` and `ι : D ⟶ (Functor.const _).obj G` are the kernel diagram and its
  cocone of inclusions. `hι U` says its leg composes with `u_U` to zero;
  `Nonempty (IsLimit (KernelFork.ofι (ι.app U) (hι U)))` says this leg is
  precisely a kernel of `u_U`. This uses Mathlib's universal property of a
  kernel, rather than requiring a literal equality to an arbitrarily chosen
  `kernel` object. Naturality of `ι` says `D.map a ≫ ι.app V = ι.app U`,
  so the transition is the unique inclusion of those kernels. In particular,
  no arbitrary diagram or arbitrary transition morphisms are substituted.
- The hypothesis `hG` quantifies over every étale object `V` and every section
  `s`. Membership of `C.genericVanishingSieve G s` in the small étale topology
  means exactly that a covering sieve consists of arrows on which the
  restricted section is killed by some affine-open unit. The existential open
  in the definition of this sieve is inside the quantification over the arrows,
  so it may depend on the covering member as the node requires.
- `IsIso (colimit.desc D { pt := G, ι := ι })` is the requested assertion
  that the canonical colimit map to `G` is an isomorphism.

The conclusion existentially packages the constructed diagram and cocone together
with their pointwise kernel universal properties and the isomorphism assertion.
This is the node's construction followed by its conclusion. It is equivalent to
using the chosen `kernel (C.affineOpenUnit U G)` objects: unique kernel isomorphisms
commute with the legs, hence with all transitions, and identify the canonical
colimit maps. No extra hypothesis on the curve or sheaf is required. In particular,
this formulation needs no new definition node and no proof hidden in a definition.

Dependency declarations read and used (the single import transitively supplies
these modules):

- `WeilConjectures.AlgebraicGeometry.Curve`: `AlgebraicGeometry.IsCurve`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.CategoryTheory.Sites.Sheaf`: `CategoryTheory.Sheaf`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`:
  `AlgebraicGeometry.Scheme.smallEtaleTopology`; its objects are
  `AlgebraicGeometry.Scheme.Etale` from `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.upperStar`, `lowerStar`, and
  `upperStarLowerStarAdjunction`, used through `Scheme.affineOpenUnit`.
- `Mathlib.CategoryTheory.Sites.Abelian`: `CategoryTheory.sheafIsAbelian`,
  providing the category in which the recorded kernel notion lives.
- `Mathlib.CategoryTheory.Limits.Shapes.Kernels`: `KernelFork.ofι` and
  `IsLimit` express exactly the universal property of the recorded kernel.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `CategoryTheory.Limits.colimit.desc`
  expresses the canonical map associated to a cocone.
- `WeilConjectures.AlgebraicGeometry.FunctionFieldLimit`:
  `Scheme.NonemptyAffineOpens` and its nonempty/directed instances.
- `WeilConjectures.AlgebraicGeometry.Curve.GenericComparison`:
  `Scheme.affineOpenUnit`, `Scheme.genericVanishingSieve`.

The source place was read in `GenericComparison.lean`: lines 98–130 give the unit
and covering sieve, and lines 156–201 construct the diagram and prove precisely
this canonical map is an isomorphism inside the acyclicity proof. There is no
standalone declaration for this intermediate assertion. The referenced blueprint
Markdown is not materialized in this clone; the node explicitly names this Lean
construction as its precise source, and that source was available and read.

Edge cases checked: integrality excludes the empty scheme and gives a nonempty
index category; intersections of nonempty affine opens contain the generic point
and contain another affine open. Zero-dimensional integral curves are allowed.
When `C` is affine, the index includes `C` and its unit kernel is zero; later,
smaller opens can still contribute nonzero kernels, as required. The zero sheaf
satisfies the hypothesis and the conclusion. Sections on an empty étale object
are permitted; the covering-sieve formulation includes the empty covering there.
No restriction on characteristic, smoothness, properness, or exact dimension is
introduced. The universe `u` is arbitrary, and the coefficient groups lie in
`u + 1` as in the source's small étale sheaf category.

Searches for reuse:

- `msearch.py ... leansearch "filtered colimit of kernels of open restriction
  units of an etale sheaf"`: service unavailable (Internal Server Error).
- `msearch.py ... leanfinder "An etale sheaf whose sections locally vanish on
  nonempty affine opens is the filtered colimit of kernels of restriction
  units"`: eight hits about sections over affine limits and unrelated results;
  no match to the statement.
- `msearch.py ... loogle "CategoryTheory.Limits.kernelFunctor,
  CategoryTheory.Subobject.toFunctor"`: no hits, unknown `kernelFunctor`.
- `msearch.py ... grep "genericVanishing|affineOpenUnit|kernel.*colimit"
  CategoryTheory/Sites`: no hits.
- Direct `rg` in Mathlib's CategoryTheory and in both `WeilConjectures` and
  `lean/Sheaf` for kernel functors, generic vanishing, affine-open units, and
  kernel colimits: the source construction above is the only relevant hit;
  the project's telescope-colimit result is unrelated.
- Direct search for the item id in `WeilConjectures`: no match.
- Direct search for the proposed declaration name in Mathlib,
  `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`: no match.

No statement correction, unusable dependency, or statement dispute was found.

## Second reading by J1

I independently compared the node, its Stacks/blueprint source place, and
`Sheaf/AlgebraicGeometry/Curve/GenericVanishingKernelColimit.lean`.
The correspondence is as follows.

- The source's algebraically closed field is Lean's `{k : Type u} [Field k]
  [IsAlgClosed k]`; the universe is unrestricted.
- The integral curve over `k` is introduced by `{C : Scheme.{u}}`,
  `f : C ⟶ Spec (.of k)`, `[IsCurve f]`, and `[IsIntegral C]`. These are the
  recorded declarations `AlgebraicGeometry.IsCurve` and
  `AlgebraicGeometry.IsIntegral`; no smoothness, properness, exact dimension,
  or extra Noetherian hypothesis is added.
- The abelian etale sheaf is
  `G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}`, using the recorded
  `CategoryTheory.Sheaf`/`smallEtaleTopology` notions.
- The reverse-inclusion index is
  `C.NonemptyAffineOpensᵒᵖ`; the source's `j_U` and `u_U` are rendered by
  `C.affineOpensDiagramι.app U.unop` and
  `C.affineOpenUnit U.unop G` (with `U` appropriately unop'ed).
- The kernel diagram and its inclusion cocone are existentially introduced as
  `D : C.NonemptyAffineOpensᵒᵖ ⥤ Sheaf ...` and
  `ι : D ⟶ (Functor.const ...).obj G`. The equation
  `hι : ∀ U, ι.app U ≫ C.affineOpenUnit U.unop G = 0` and
  `Nonempty (IsLimit (KernelFork.ofι (ι.app U) (hι U)))` give exactly the
  pointwise kernel universal property. Naturality of `ι` supplies the kernel
  transitions and cocone compatibility.
- The source's generic-vanishing covering condition is exactly
  `∀ (V : C.Etale) (s : G.obj.obj (op V)),
  C.genericVanishingSieve G s ∈ C.smallEtaleTopology V`; the affine open may
  depend on each covering arrow as in `genericVanishingSieve`.
- The conclusion is exactly the isomorphism of the canonical colimit map,
  `IsIso (colimit.desc D { pt := G, ι := ι })`, using the recorded colimit API.
  Quantifier order and conjunction structure agree with the node.

No mismatch was found and no repair was needed. The existential formulation is
adequate: kernel universal properties together with cocone naturality force the
unique transition maps induced by the unit factorizations, so it expresses the
source's canonical kernel diagram up to unique kernel isomorphism.

Edge cases checked: `IsIntegral C` supplies nonemptiness, so the affine-open
index is nonempty and filtered; the empty scheme is therefore excluded exactly
as in the source. The affine case (including its zero kernel at the whole open),
zero sheaf, sections on empty etale objects, `n = 0` (there is no `n` in this
statement), and arbitrary characteristic are all covered. No universe restriction
beyond the source's `u` and coefficient category `u + 1` is present.

I searched Mathlib, `WeilConjectures`, and `lean/Sheaf` with `rg` for
`genericVanishing`, `affineOpenUnit`, kernel-colimit variants, and the proposed
declaration; only the source construction in `GenericComparison.lean` was
relevant. The recorded LeanSearch, LeanFinder/Loogle, and grep searches found
no existing declaration. The single-file compilation via `scompile.py` passed
without errors or warnings.
