## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleSetInverseImageExact` states
`AlgebraicGeometry.etaleSetInverseImage_exact`; its only proof is `sorry`.
It introduces no definition, axiom, instance or file-local notation.
The node is unchanged except for its `lean` record.

Hypothesis and clause correspondence:

- Arbitrary schemes T and T': `{T T' : Scheme.{u}}`. Arbitrary morphism h:
  `(h : T' ⟶ T)`, with no etaleness, properness, finiteness or nonemptiness assumption.
- The small etale sites are `T.smallGrothendieckTopology @Etale` and
  `T'.smallGrothendieckTopology @Etale`, definitionally the recorded
  `Scheme.smallEtaleTopology`. Their object categories are `T.Etale` and `T'.Etale`.
- Base change V ↦ V ×_T T' is `MorphismProperty.Over.pullback @Etale ⊤ h`.
  Continuity is the first conjunct `IsContinuous` with these two topologies.
  The recorded `Etale.isContinuous_overPullback` supplies this instance for elaboration.
  Its underlying result `Scheme.isContinuous_overPullback` uses base-change stability
  of coverings and pullbacks, giving the Stacks continuity conditions of the node.
- Set-valued sheaves use coefficients `Type (u + 1)`, matching the site's object
  and morphism universes and the established project's etale-set-sheaf encoding.
- The induced inverse image is the existing
  `Functor.sheafPullbackConstruction.sheafPullback` at base change and these topologies.
  Its definition is `sheafToPresheaf ⋙ b.op.lan ⋙ presheafToSheaf`: presheaf inverse
  image followed by sheafification. This is definitionally the already landed
  `Scheme.etaleSetPullback h`, not a new inverse-image definition.
- Left adjunction to the specified direct image is the second conjunct
  `Nonempty (sheafPullback … ⊣ b.sheafPushforwardContinuous …)`.
  `sheafPushforwardContinuous` is defined by precomposition with `b.op`, so its
  sections are exactly F(V ×_T T') and its restriction maps are F on the base-changed
  maps. No arbitrary right adjoint or arbitrary inverse-image functor is used.
- Preservation of finite limits is the third conjunct `PreservesFiniteLimits` of
  this same inverse image. Preservation of finite colimits is the fourth conjunct
  `PreservesFiniteColimits` of the same inverse image.
- The resulting morphism of sites T'_et → T_et is expressed by continuity and these
  two preservation conjuncts, exactly the inline morphism-of-sites convention in
  `def-weil-pbc-sites-and-cohomology`(3). There is no different bundled structure to
  construct, and no additional conclusion such as abelian or ring inverse image.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`; schemes are locally affine locally ringed spaces,
  with locally ringed space morphisms.
- `def-weil-pbc-etale-site`: `Scheme.smallEtaleTopology`,
  `Mathlib.AlgebraicGeometry.Sites.Etale`, and `Scheme.Etale`,
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`; the latter is the etale Over category.
- `lem-weil-pbc-etale-base-change-continuous`: `Etale.isContinuous_overPullback`,
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`. Its signature allows any
  scheme morphism and gives continuity for precisely the two displayed topologies.
- `def-weil-pbc-sites-and-cohomology`(3): its record explicitly specifies Mathlib's
  `Functor.IsContinuous`, `Functor.sheafPushforwardContinuous` and
  `Functor.sheafPullbackConstruction.sheafPullback` / `sheafAdjunctionContinuous`,
  with the morphism condition inline as finite-limit and finite-colimit preservation.
  The relevant signatures and docstrings were read in
  `Mathlib.CategoryTheory.Sites.Continuous` and `Mathlib.CategoryTheory.Sites.Pullback`.
  Its primary recorded `Sheaf.H'` is the cohomology clause (2) and is not needed here.
  These existing notions suffice; no dependency module is needed.

The theorem docstring follows all four proof steps: continuity and the sectionwise
pushforward from `lem-weil-pbc-etale-base-change-continuous`; adjunction and finite
limits from `lem-weil-pbc-etale-inverse-image-algebraic-structures`(1); finite colimits
from `lem-weil-pbc-left-adjoint-preserves-colimits`; the morphism-of-sites conclusion
from `def-weil-pbc-sites-and-cohomology`(3).

Sources checked directly: [Stacks 03Q1](https://stacks.math.columbia.edu/tag/03Q1),
assertion (2), [Section 03PZ](https://stacks.math.columbia.edu/tag/03PZ), Definition
59.36.1, and [Definition 00X1](https://stacks.math.columbia.edu/tag/00X1).
These agree with the node; no statement correction or dispute is needed.

Edge cases checked before writing: either scheme may be empty, h may be an identity
or an arbitrary non-etale map. No binder excludes these cases. Finite-limit
preservation includes the empty limit (terminal sheaf); finite-colimit preservation
includes the empty colimit (initial sheaf), including on the empty scheme where the
sheaf category is equivalent to the terminal category. No pointed or additive
coefficient assumption has been imposed. The universe u is explicit; there are no
auto-bound variables or universes, nor an independent small index universe.

Searches for an existing exact statement:

- `msearch.py leansearch`, query "inverse image sheaves of sets small etale scheme
  finite limits finite colimits": unavailable, Internal Server Error; no verdict
  inferred from the unavailable search.
- `msearch.py leanfinder`, query "Inverse image of sheaves of sets on the small
  etale site of a scheme preserves finite limits and finite colimits": eight hits,
  including `Functor.sheafPullbackConstruction.preservesFiniteLimits` and the
  small-category variant. These are generic conditional finite-limit results, not
  the scheme-specific full exactness and adjunction statement of this node.
- `msearch.py loogle`, query
  `CategoryTheory.Functor.sheafPullbackConstruction.preservesFiniteLimits, PreservesFiniteColimits`:
  zero hits, unknown unqualified identifier `PreservesFiniteColimits`.
- `msearch.py grep`, query `preservesFiniteLimits|PreservesFiniteColimits` in
  `CategoryTheory/Sites`: 25 hits. Pullback.lean gives conditional finite-limit
  preservation; the finite-colimit hits concern point fibers, not scheme inverse image.
- `rg` of the upstream project for `isContinuous_overPullback`, finite-limit
  preservation of upperStar and upperStar definitions: continuity is available,
  but the source's etale upperStar and its exactness require an abelian Grothendieck
  coefficient category, which excludes sheaves of sets. Read the full source
  signatures and their explanatory docstrings in UpperLowerStar/Defs.lean.
- `rg` of landed Sheaf modules for `etaleSetPullback` finds its definition in
  EtaleSheaves.lean, and finite-limit preservation as part of the larger
  `etaleInverseImageAlgebraicStructures` statement, but no full exactness statement
  for set inverse image. The present signature uses the existing construction
  directly, so it does not add another notion or require another definition node.
- `rg` for the item id in the upstream project: no result. `rg` for the proposed
  name `etaleSetInverseImage_exact` in Mathlib, upstream, landed Sheaf modules and
  `dag/lean_names_upstream.json`: no name collision.

Validation: local `lcompile.py` accepted the module in 2.0 seconds with no errors
or warnings. Final server compilation and preflight are run by the delivery dry run.

## Second reading by M1

I reread the node, its source references, all recorded statement dependencies, and
the module independently. The correspondence is exact:

- The node's objects `T`, `T'`, and `h : T' → T` render as `{T T' : Scheme.{u}}`
  and `(h : T' ⟶ T)`; no extra hypotheses or instances are introduced.
- The two small étale sites render as
  `T.smallGrothendieckTopology @Etale` and
  `T'.smallGrothendieckTopology @Etale`, with the corresponding `Scheme.Etale`
  categories supplied by the recorded Mathlib site declaration.
- Base change `V ↦ V ×_T T'` renders as
  `MorphismProperty.Over.pullback @Etale ⊤ h`. Its continuity is the first
  conjunct, with the existing `AlgebraicGeometry.Etale.isContinuous_overPullback`
  instance supplying precisely this fact.
- Set-valued sheaves render with coefficient category `Type (u + 1)`, and the
  inverse image renders as
  `Functor.sheafPullbackConstruction.sheafPullback` on that base-change functor
  and those two topologies. This is definitionally the existing
  `Scheme.etaleSetPullback` construction.
- The direct image is exactly
  `b.sheafPushforwardContinuous (Type (u + 1)) ...`; the second conjunct is
  `Nonempty (inverseImage ⊣ directImage)`, matching the stated sectionwise
  formula and left-adjoint requirement.
- The final two conjuncts are `PreservesFiniteLimits inverseImage` and
  `PreservesFiniteColimits inverseImage`, with no added abelian, ring, or
  cohomological conclusion. Their conjunction with continuity is precisely the
  morphism-of-sites exactness condition cited by the node.

Edge cases remain covered: either scheme may be empty, `h` may be an identity or
an arbitrary morphism, and no nonemptiness, finiteness, characteristic, or
Noetherian assumption is present. Finite limits and colimits include their empty
instances. The single universe `u` is shared by schemes, sites, and coefficients;
there is no independent vacuous universe.

Searches were checked in Mathlib, the slopmaster2 source, and landed `Sheaf`
modules using `rg`, plus the recorded LeanSearch, LeanFinder, Loogle, and grep
queries in `searches.jsonl`. LeanSearch was unavailable; the other searches found
only generic conditional pullback results or the existing `etaleSetPullback`, not
this exact scheme-specific theorem. No name collision or duplicate statement was
found. No mismatch was found and no source, node, dependency, or module change was
needed.
