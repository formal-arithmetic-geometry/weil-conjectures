## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceCoherentFppfStack` states
`AlgebraicGeometry.AlgebraicSpace.coherent_fppf_stack`, with proof `sorry`.
Source read: `literature/stacks-project/quot.tex`, Situation 08KB
(`situation-coherent`, lines 879–910), Tag 08W5
(`lemma-coherent-fibred-in-groupoids`, lines 913–949), and Tag 08KC
(`lemma-coherent-stack`, lines 978–1044). The Lean states fppf stack descent,
not merely etale descent. No statement correction is needed.

The current source already has precisely the required category:
`AlgebraicGeometry.AlgebraicSpace.CoherentModuli` and
`CoherentModuli.category`, in `Sheaf.AlgebraicGeometry.SpaceCoherentStackGeneral`.
I read its complete definitions, including `Hom`, the fibre-map laws, the
multiplication-normalized identity, the tensor-normalized composition, the
category laws, and the projection to `Over S`. I also checked that exact module
with `scompile.py --source Sheaf.AlgebraicGeometry.SpaceCoherentStackGeneral`.
It places no separatedness hypothesis on the category itself. Its theorem
`coherent_stack_general` does assume separatedness and concludes algebraicity;
that theorem is neither used nor re-recorded as this fppf-stack assertion.
There is no duplicate definition, arbitrary choice of module, or quotient of
objects by isomorphism classes in this delivery.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Scheme S and size convention | Explicit `universe u`, `{S : Scheme.{u}}`; the existing space/site/module universes are retained. No extra size equality, smallness restriction or essential-smallness hypothesis is imposed. |
| Algebraic spaces X, B over S | `{X B : AlgebraicSpace S}`. `AlgebraicSpace` is the full subcategory of fppf sheaves with representable diagonal and surjective etale scheme atlas. |
| Finitely presented f:X→B | `(f : X ⟶ B) (hfp : ProperQuotFinitePresentation f)`. This predicate is local finite presentation on all compatible etale charts, quasi-compactness, and quasi-compactness of the diagonal. No separatedness or flatness of f is added. |
| Every S-scheme T and map b:T→B | A `CoherentModuli f` object has `base : ProperQuotTest B`, the actual `CostructuredArrow yoneda B.obj.obj`; its `base.left` is T over S and `base.hom` is b. The projection in `CoherentModuli.category` forgets to this T. All S-schemes and all such b occur. |
| Sheaf fibre product X×_B T | `properQuotFibre f base`, explicitly constructed from the sheaf pullback with its algebraic-space property from `fibreProduct_isAlgebraicSpace`. |
| Module M on its small etale ringed site | `module : (properQuotFibre f base).Modules`, using the existing structure sheaf of regular functions. |
| Quasi-coherent | `CoherentModuli.quasiCoherent : module.IsQuasicoherent`, Mathlib's local presentation predicate, specialized by `AlgebraicSpaceQuasiCoherentModule`. |
| Finite presentation, locally a finite-free cokernel | `CoherentModuli.finitePresentation : module.IsFinitePresentation`, Mathlib's finite local presentation predicate. |
| Flat over T on every etale chart | `CoherentModuli.flat` quantifies over every `U : (properQuotFibre f base).EtaleSite` and uses `((schemeRestriction ... U).obj module).IsFlatOver` for the actual scheme map to T. The recorded affine-local scheme `IsFlatOver` agrees with the stalkwise condition for these quasi-coherent restrictions; this is exactly the encoding already adopted by the proper-Quot dependency. |
| Proper support | `CoherentModuli.properSupport` is the existential `Z, i` with `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom`, `MapIsProper (i ≫ properQuotSnd f base)`, and a module G with `G.IsQuasicoherent`, `G.IsFiniteType`, and `Nonempty ((moduleDirectImage i).obj G ≅ module)`. Thus it retains exactly the specified closed carrier, proper projection, finite type module, and pushforward isomorphism. |
| Arrows over v and equation b=b₁v | `CoherentModuli.Hom.base : A.base ⟶ C.base` is a costructured-arrow morphism, including that commuting equation; `Hom.iso` is `(moduleTensorPullback (properQuotFibreMap f base)).obj C.module ≅ A.module`, in the direction required by the node. |
| Canonical composition and identities | `CoherentModuli.composition` uses the inverse of the existing pure-tensor-normalized `moduleTensorComposition`, followed by pullback of the second iso and the first iso. `identity` uses `moduleTensorPullbackId`. The instance has precisely these operations, not a chosen arbitrary category structure. |
| Groupoids and pullback transitions | `IsFppfModuliStack (CoherentModuli.category f)` includes `IsFibredInGroupoids`, namely `IsFibered` and strong cartesianness of every arrow. Because the specified arrows are pullback isomorphisms, these are exactly the lifts and transitions in the node, retaining all automorphisms. |
| Big fppf site of S | The existing `CategoryTheory.IsFppfModuliStack` uses `(Scheme.fppfTopology.over S)` on `Over S`, not the etale topology. |
| Isomorphism presheaves are sheaves and all object descent is effective | The second part of `IsFppfModuliStack` quantifies over every covering sieve and every diagram over its arrows, and supplies a colimit cocone with the prescribed base cocone. In a category fibred in groupoids this is the standard total-category formulation of effective descent and unique gluing of arrows; the existing definition's docstring spells out this interpretation. |

The theorem docstring contains all eight steps of the node's natural-language
proof, naming the nodes used in each step. Every theorem proof in this delivery
is `sorry`; there are no definition or instance declarations.

Dependency declarations used/read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `def-weil-size-convention` is a metatheoretic convention; its record expressly
  requires explicit universe binders, not an imported counterpart object.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `IsAlgebraicSpace`, `IsRepresentableWith`, `EtaleSite`, `structureSheaf`, `Modules`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace` and its actual sheaf pullback interface.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and
  the slice instances supporting Mathlib `SheafOfModules.IsQuasicoherent`
  and `SheafOfModules.IsFinitePresentation`. The full Mathlib signatures and
  docstrings of both predicates were read in `Quasicoherent.lean`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `moduleDirectImageModel`, `moduleDirectImage`, `moduleTensorPullback`,
  `moduleTensorAdjunction`, `moduleTensorSection`, with their normalized
  chart-limit/adjunction definitions.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `Scheme.Modules.IsFlatOver`; the full affine-local definition was read.
- `Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor`: `ProperQuotTest`,
  `properQuotFibre`, `properQuotSnd`, `ProperQuotFinitePresentation`,
  `properQuotFibreMap`. I read the complete module and the admissible-target
  predicates, which the existing `CoherentModuli` uses unchanged.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsLocallyOfFinitePresentation`, `MapIsProper` and their chart/topological
  definitions; the complete signatures and docstrings were read.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`,
  `Scheme.fppfTopology`; the full definitions were read.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsFibredInGroupoids`; the total-category definition and
  `IsModuliStack` docstring were read. The latter is etale and is not used
  in place of the required fppf predicate.
- The already landed definition node `def-sfb-fppf-stackification` is added
  to `stmt_deps`, as permitted by brief-stage2 section 5. Its module
  `Sheaf.CategoryTheory.SiteStackification` gives
  `CategoryTheory.IsFppfModuliStack`. I read its complete signature and docstring.
  No dependency node is edited and no new node is created.

All recorded proof-dependency modules that exist are imported with plain
`import`, except those also public statement dependencies. Proof nodes with no
recorded declaration need no placeholder import: these are
`lem-sfb-space-fppf-qcoh-descent`, `lem-trf-fppf-covering-is-fpqc`,
`lem-sfb-scheme-etale-module-exact-finiteness-comparison`, and
`lem-sfb-space-module-proper-carrier-support`. The flat affine criterion is the
existing Mathlib predicate from `Mathlib.AlgebraicGeometry.Morphisms.Flat`.

Edge cases checked against the definitions and source:

- Zero modules are allowed. The proper-support convention admits the empty
  closed carrier with its zero module, even when X_T itself is not proper.
- Empty test schemes and the empty covering of an empty scheme are retained:
  the site predicate quantifies over all covering sieves, without a Nonempty
  assumption or a choice of a covering member in the statement.
- X or B may be empty; objects require actual maps b, with no assumed point of B.
- Arbitrary, including non-flat, transition maps are allowed. Only f is finitely
  presented. There is no extra hypothesis that X or X_T is flat over the base.
- Different maps b are retained, and arrows require their actual equality after
  composition; an empty isomorphism presheaf is not silently discarded.
- All module isomorphisms and automorphisms are retained, rather than taking
  isomorphism classes. No characteristic assumption is made.

Searches actually run:

1. `msearch.py ... leanfinder` with query
   `Flat finitely presented quasi coherent modules with proper support form a stack in groupoids for the fppf topology`:
   eight results, all generic finite-presentation/quasi-coherence declarations
   (`SheafOfModules.quasicoherentDataOfIsFinitePresentation`,
   `QuasicoherentData.IsFinitePresentation`, `instIsQuasicoherentOfIsFinitePresentation`,
   `isFinitePresentation`, `IsFinitePresentation`,
   `QuasicoherentData.IsFinitePresentation.isFinite_presentation`,
   `IsFinitePresentation.exists_quasicoherentData`, `QuasicoherentData`).
   None asserts the moduli-stack theorem.
2. `msearch.py ... loogle` with query
   `CategoryTheory.IsStack, SheafOfModules.IsFinitePresentation`:
   zero hits; the service explicitly reported unknown identifier
   `CategoryTheory.IsStack`. This is a failed name-based candidate query,
   not evidence that no stack API exists.
3. `msearch.py ... grep` with expression
   `CoherentStack|coherentStack|FlatCoherent|flatCoherent|IsStack`
   in Mathlib `AlgebraicGeometry`: zero hits.
4. `rg` on both project roots with coherent-stack, `CoherentModuli`,
   `coherent_fppf_stack`, and `IsFppfModuliStack` patterns found the existing
   coherent-family construction in `SpaceCoherentStackGeneral`, the scheme-only
   `FlatCoherentModuli`, and `SiteStackification`. The first is reused for
   objects/arrows and the last for the topology-correct stack predicate.
   The algebraicity theorem has additional separatedness and an etale-algebraic
   conclusion, so it is not an exact existing match for this item.
5. `grep -rn lem-sfb-space-coherent-fppf-stack lean/WeilConjectures`
   returned no hit. Exact new declaration-name search in Mathlib/project
   sources and `dag/lean_names_upstream.json` found no collision.

Import ownership for the maintainer: the already landed
`SpaceCoherentStackGeneral` owns `CoherentModuli` even though its main theorem
is downstream of this item. This delivery imports it for those definitions only;
it does not add the downstream theorem to the item's DAG dependencies and does
not use its algebraicity result. Under the stage-2 rule excluding cycle-closing
proof imports, do not insert a reciprocal import of this module into
`SpaceCoherentStackGeneral` while those shared definitions remain there.
A later source reorganization can put the common definitions in a prerequisite
module. Copying those definitions here would violate the one-definition rule.
No false statement or mathematical discrepancy was found.

Validation: standalone `scompile.py` passed for the sandbox module (32.7 seconds)
and its library-path probe (10.9 seconds), without errors or warnings.
`deliver2.py Q20 lem-sfb-space-coherent-fppf-stack --no-push` then printed
`OK (dry run)` after server preflight and compilation. The actual delivery
uses the same prescribed `deliver2.py` wrapper.

## Second reading by Q20

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
