## Worker report

The saved packet's initial required dry run timed out locally and on the server. The
concrete theorem's kernel checking was expensive even though elaboration took eight seconds.
The current repair expresses its five ambient clauses once as
`CategoryTheory.Adjunction.OpenProjectionFormulaClauses` over arbitrary monoidal categories,
then specializes this exact conjunction to the recorded derived categories, adjunction,
canonical monoidal pullback and Koszul braidings. This is an organizational helper for this
node's own statement: no hypothesis, clause, map or independent notion is added or removed.
The restricted clauses stay explicit. All helper data is real; only the theorem is postponed.

The module uses the published declaration underlying the transparent `bcoOpenAdjunction`
alias. Its upstream module is imported directly because the alias module's import path exceeds
100 characters. No adjunction is copied. The named underived and derived monoidal instances
are specializations by `inferInstance`, and the pullback monoidal instance specializes
`monoidal_leftDerivedUpperStar`. These retain the published structures definitionally.

The item is stated by
AlgebraicGeometry.ProEtale.CondensedRing.condensed_open_exceptional_projection_formula.
Its sole theorem has proof `sorry`. The helpers construct the actual maps and structures,
using existing objects throughout; no additional theorem is postponed.

Hypotheses and objects, matched individually to the node:

- A prime ℓ: `(ℓ : ℕ) [Fact ℓ.Prime]`.
- A field k of positive characteristic different from ℓ: `{k : Type u} [Field k]`,
  `[Fact (ringChar k).Prime]`, and `[Fact (ringChar k ≠ ℓ)]`.
- Separated finite-type k-schemes: `{U X : Over (Spec (.of k))}` with
  `[LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom]`, and the three
  corresponding instances for X. Locally finite type and quasi-compact mean finite type.
- A morphism over k: `(j : U ⟶ X)`; the actual scheme map is `j.left`.
- An open immersion: `[IsOpenImmersion j.left]`.
- An arbitrary commutative condensed ring: `Λ : Sheaf (coherentTopology Profinite.{u})
  Ab.{u + 1}` with `[MonObj Λ] [IsCommMonObj Λ]`. This is the unbundled presentation of the
  recorded `Profinite.CondensedRing` (the existing `Mon` category), with commutativity.
  There is no assumption of a topological presentation or of finiteness for Λ.
- Pulled-back coefficient objects: `condensedRingObj Λ U.left` and
  `condensedRingObj Λ X.left`, exactly the dependency's p-star construction.
- C_U and C_X: the ordinary unbounded `DerivedCategory (Mod (Sheaf ... Ab) ...)`.
- e: `(openImmersionLowerShriek Λ j.left).mapDerivedCategory`, applying the existing exact
  module extension by zero levelwise.
- r: `moduleObjectDerivedPullback Λ j.left`, the named total left derived functor of the
  complete module pullback, not a pullback of the derived abelian functor.
- The tensors `⊗`, morphism tensors `⊗ₘ` and whiskering `▷` use the published relative
  K-flat derived monoidal structures, which the recorded derived tensor is defined from.
- η and ε: `condensedOpenDerivedAdjunction Λ j.left` transports the published exact derived
  open adjunction by the inverse of `leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion`.
- μ: `Functor.LaxMonoidal.μ (moduleObjectDerivedPullback Λ j.left)` uses the existing
  `monoidal_leftDerivedUpperStar` through the transparent specialization
  `moduleObjectDerivedPullbackMonoidal`. That published monoidal structure has tensorator
  inverse to `leftDerivedUpperStarTensorIso`, characterized by the actual derived counits.

Conclusion, clause by clause in the order of the conjunction:

The first conjunct unfolds `OpenProjectionFormulaClauses` at
`condensedOpenDerivedAdjunction Λ j.left`, `condensedDerivedBraiding Λ U.left`, and
`condensedDerivedBraiding Λ X.left`. In its definition `C=C_U`, `D=C_X`,
`e=(openImmersionLowerShriek Λ j.left).mapDerivedCategory` and
`r=moduleObjectDerivedPullback Λ j.left`. Its five conjuncts are exactly items 1–5 below.
Its generic projectionMap uses `curriedTensor`, definitionally the dependency's
`derivedTensor`. `condensedOpenProjection` names this very same natural transformation.
Items 6 onward remain the theorem's explicit remaining conjunction.

1. `IsIso (condensedOpenDerivedAdjunction Λ j.left).unit` says the unit is invertible at
   every K; invertibility of a natural transformation is pointwise invertibility.
2. The universally quantified `IsIso (condensedOpenProjection Λ j.left K L)` gives the
   exact component in the node for every unbounded K and L. Its definition specializes
   the existing `Adjunction.projectionMap` at the relative tensors and actual μ natural
   transformation. That generic definition is e applied to the transpose
   `(η_K ▷ rL) ≫ μ_(eK,L)`, followed by ε_(eK tensor L). Functoriality expands it to
   precisely the three-factor composite displayed in the node.
3. The next equality for arbitrary `a : K ⟶ K'` and `b : L ⟶ L'` is naturality in both
   arguments, with source arrow `e.map (a ⊗ₘ r.map b)` and target arrow `e.map a ⊗ₘ b`.
4. The `homEquiv` equality gives precisely the stated adjoint-of-unit description,
   with transpose `(η_K ▷ rL) ≫ μ_(eK,L)`.
5. The next equality identifies q with e of the input braiding, the dependency's
   `projectionFormulaMap L K`, and the output braiding. The braidings are the existing
   Koszul braiding specialized by `condensedDerivedBraiding`, not arbitrary structures.
6. The final four clauses specialize to `Profinite.padicAlgClRingObj ℓ`: invertible restricted
   unit, invertibility of every `((condensedQlbOpenProjection ℓ j).app K).app L`, its naturality, and
   equality of its underlying ambient morphism with `condensedOpenProjection` at `K.obj`
   and `L.obj`. Thus the isomorphism is in the full bounded constructible subcategory and
   is the restriction of this actual component. The coefficient is the finite-subextension
   continuous-function sheaf, not the full sheaf of all continuous algebraic-closure maps.

Dependency declarations used (all signatures and their documentation were inspected):

- Sheaf.Topology.ProfiniteCondensedRing: `Profinite.CondensedRing`, the existing Mon encoding.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic: `coefficientRing`,
  `condensedRingObj`, and its commutativity instance.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs:
  `openImmersionLowerShriek` and `openImmersionLowerShriekUpperStarAdjunction`; the former
  is restriction along α followed by the published linear extension by zero.
- Sheaf.Paper.CondensedModuleDerivedPushpull: `moduleObjectDerivedPullback`, whose body is
  `(upperStar Λ f).leftDerivedFunctor`.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek:
  `derivedOpenImmersionLowerShriekUpperStarAdjunction` and
  `leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion`.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal:
  `monoidal_leftDerivedUpperStar`; the tensorator is the inverse of the published oplax map.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom and Derived.Tensor:
  `derivedHom`, `derivedTensor`, the K-flat monoidal structure and its derived universal property.
- WeilConjectures.CategoryTheory.Adjunction.ProjectionMap:
  `CategoryTheory.Adjunction.projectionMap` and `projectionMapTranspose` construct the
  actual canonical map used in both component helpers, including its unit and counit.
- WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula and its imports:
  `CategoryTheory.Adjunction.projectionFormulaMap`, the actual adjoint of the unit composite,
  and `CategoryTheory.Adjunction.HasProjectionFormula`.
- WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided:
  `DerivedCategory.braidedCategory`, descending the signed braiding on complexes.
- WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic:
  `Profinite.padicAlgClRingObj` and `padicAlgClCondensedRing`.
- Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale publicly retains
  `AlgebraicGeometry.ProEtale.BoundedConstructible` and `boundedConstructible`, the full
  subcategory with bounded constructible cohomology, without derived completeness.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible:
  `boundedConstructibleUpperStar`, `boundedConstructibleOpenImmersionLowerShriek`, and their
  restricted canonical monoidal structures. Its setting is exactly the explicit Over binders.
- Sheaf.AlgebraicGeometry.ProEtale.CondensedRing.
  BoundedConstructibleOpenImmersionLowerShriekUpperStarAdjunctionAlias:
  `bcoOpenAdjunction` is a transparent alias for the exact published
  `boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction` used directly here;
  its definition was read and compared with the underlying declaration. This avoids
  importing the alias module with its unrenderably long import path.

The other recorded proof dependency modules are imported as non-public imports. The theorem's
docstring retains all seven steps of the node's natural-language proof, including relative
balancing, unbounded direct-sum totalization, K-flat preservation, identification of the actual
lax tensorator, symmetry and restriction through the full subcategory.

Source checked: blueprint main-20261015, sec-six-functors-basics/sk-lem-int-tensor/
det-lem-int-tensor-projection.proof.md, Open immersions, sheaves and Derived version.
The source constructs the adjoint of the unit and proves the derived formula using K-flat
representatives; the module does not substitute an endpoint isomorphism for that map.
The current published BoundedConstructible and Monoidal sources were also read using
scompile.py --source, since the local framework source is older in its Over binders.

Edge cases checked on the statements and constructions: j may be the identity or have empty
domain; K and L may be zero; unbounded complexes are allowed; Λ may be the zero condensed ring
or a non-flat condensed ring. No nonemptiness or boundedness is imposed in the ambient clauses.
The restricted tensor clauses use only the specified algebraic-closure coefficient; they do
not assert bounded tensor closure for arbitrary Λ (which fails already over ℤ/4).
There is no characteristic-zero case in the source's setting. The universe u remains arbitrary,
with sites on Scheme.{u} and coefficients Ab.{u+1}, exactly as in the dependencies.
No statement correction, new DAG node or dependency module is needed. No disputed statement.

Searches (retained searches.jsonl records the earlier attempt's exact tool responses):

- msearch.py LeanSearch, 'Extension by zero projection formula for derived module objects on
  the pro etale site with condensed coefficients': eight unrelated derived/condensed hits;
  no exact formula.
- msearch.py LeanFinder, 'For an open immersion the canonical projection map on derived
  condensed module objects extension by zero tensor derived pullback is an isomorphism':
  eight restriction/open-immersion hits, including Scheme.Modules.restrictAdjunction;
  none state the condensed relative derived assertion.
- msearch.py Loogle, 'CategoryTheory.Adjunction.projectionFormulaMap,
  CategoryTheory.Functor.LaxMonoidal.μ': no hit; the first identifier is not in Mathlib.
- msearch.py grep, 'openImmersionProjection|exceptionalProjection|projectionFormulaMap':
  no Mathlib hits.
- rg in WeilConjectures and lean/Sheaf for 'open.*projection|projection.*open|condensedOpen|
  open_exceptional': existing finite-coefficient and ringed-site projection formulas and
  integral-system interfaces occur, but no assertion on these condensed module-object maps.
- rg for the exact item id and declaration names in WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json: no existing declaration of this item. No name collision found.

## Second reading by N1

Author self-check of the node and final file, as required by direct dispatcher delivery;
the maintainer supplies the independent review. No second agent was started.
The match above was reread against each quantified variable and each conjunction. The ambient
part uses every commutative condensed coefficient and every unbounded pair. Only the final
restricted part specializes to Ql-bar and bounded constructible objects. The equality with
`projectionFormulaMap` has source braiding K,rL and target braiding L,eK, so it has the node's
orientation. The transpose uses the unit, not its inverse. The total-derived identification
is transported with `.symm`, matching the restricted adjunction's construction. The full
subcategory arrow's `.hom` is compared with the very same ambient composite. The helper
monoidal instance is the actual published one; the explicit braiding is Koszul. All helper
data is constructed, the only sorry is the theorem, and all variables/universes are explicit.
The missing report and record were supplied; compilation diagnostics were repaired as above.
The framework's existing local irreducibility controls for DerivedCategory.monoidalClosed,
Mod.monoidalClosed and upperStarFromPoint are applied to avoid expanding internal-Hom
resolutions during definitional comparisons; these do not change any construction or signature.


## Saved-packet repair, 2026-10-18

The prescribed initial dry run of the saved packet timed out both locally and on the server.
A scratch profiler identified kernel checks of the concretely expanded braiding and projection
components as expensive (about 9, 15 and 17 seconds respectively), in addition to the theorem.
The two component helpers now specialize the existing generic `Adjunction.projectionMap`
instead of elaborating its full composite at the concrete sites. Their tensors and μ are
unchanged. The braiding and component helpers allow Lean to infer their result types from
these canonical constructions, avoiding redundant kernel comparisons with separately
elaborated result types. At that earlier repair step the theorem signature retained its component form; the current
2026-10-19 repair below replaces the ambient conjunction by its generic specialization.
No postponed theorem or new notion was added. The source declaration of the generic map and
its full transpose definition were read directly and checked against the node's formula.


## Saved-packet repair, 2026-10-19

The required first dry run returned a local and server timeout at 60 seconds. Profiling
located the remaining cost in the concrete theorem kernel check, rather than its helper
construction. The repaired theorem specializes `OpenProjectionFormulaClauses`, whose
body reproduces the full ambient conjunction with the exact projectionMap, naturality,
transpose and symmetry. This preserves every original clause, and also shares monoidal
structure arguments without repeatedly comparing expanded derived constructions.
The helper has fully bound category and morphism universes u₁, u₂, v₁, v₂. The theorem's
coefficient and site universe is still the arbitrary original u.
The named monoidal instances and all canonical map helpers are listed in lean.declarations.
The braiding specialization is instance_reducible, matching its published upstream source.
The node changes only in lean, and lean.statement has been reread verbatim from the final file.

Self-check: read the current node, the repaired module, the recorded dependency interfaces
and blueprint source. The generic helper's five conjuncts respectively give unit
invertibility, component invertibility, two-variable naturality, the unit transpose and
the same symmetric projection map. The theorem's last four conjuncts give the restricted
unit, component, naturality and equality with the ambient component for Ql-bar. The
orientation of each braiding and of the adjunction transport is unchanged. Identity,
empty-open, zero-object, arbitrary unbounded-complex and non-flat coefficient cases remain
included. No new independent definition node, dependency repair or statement correction is
needed: this only packages this item's existing clauses. The initial repaired file compiled
in 34.8/29.9 seconds in sandbox/library modes; its two style warnings were then repaired.
