## Worker report

The module Sheaf.AlgebraicGeometry.DerivedGeometricStalkConservative states
AlgebraicGeometry.Scheme.isIso_iff_isIso_geometricStalk_homologyMap. Its proof is
`sorry`; no definitions or proofs are added. The natural-language proof follows all
three DAG proof steps in the declaration docstring. No statement correction,
new node, dependency repair, or disputed statement is needed.

Hypothesis and clause correspondence:

- A scheme T: `{T : Scheme.{u}}`, with arbitrary universe u.
- K and L in D⁺(T_et), with the node's implicit abelian-group coefficients:
  `{K L : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})}`.
  Plus is the full subcategory bounded below in cohomology, not a chosen complex
  with an additional termwise boundedness condition.
- The morphism K → L: `(f : K ⟶ L)`. This is any derived morphism, including roofs,
  not just a morphism coming from a fixed pair of complex representatives.
- Invertibility in that category: `IsIso f`.
- If and only if: `↔`.
- Every geometric point: `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
  (t : Spec (CommRingCat.of Ω) ⟶ T)`. This is the algebraically closed
  field convention fixed by def-weil-pbc-scheme-conventions and def-weil-geometric-point. The field universe equals the scheme
  universe and includes its residue-field algebraic closures.
- Every integer i: `(i : ℤ)`; no restriction to nonnegative degrees.
- The induced cohomology-sheaf map: `(DerivedCategory.Plus.homologyFunctor _ i).map f`.
- Its geometric stalk map: `(pointSmallEtale t).sheafFiber.map` of that map.
- That map is an isomorphism: the final `IsIso`. This concerns the stalk of the
  cohomology sheaf itself, so no comparison to cohomology of a stalk complex is
  imposed as an extra premise.

Dependency declarations used, read with their signatures and docstrings:

- def-weil-pbc-derived-categories: Sheaf.AlgebraicGeometry.DerivedCategories,
  whose module documentation specifies D(T_et) as the derived category of
  `Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}` and refers to Mathlib's
  DerivedCategory.Plus and DerivedCategory.homologyFunctor. The module also
  imports the canonical global derived-category instances. Its torsionCohomology
  declaration is not needed: this node has no torsion hypothesis.
- DerivedCategory.Plus is Mathlib's standard-t-structure full subcategory in
  Mathlib.Algebra.Homology.DerivedCategory.TStructure. The cohomology functor on
  Plus is DerivedCategory.Plus.homologyFunctor in
  Mathlib.Algebra.Homology.DerivedCategory.Plus, inclusion followed by the usual
  DerivedCategory.homologyFunctor (HomologySequence).
- def-weil-pbc-geometric-stalks: CategoryTheory.GrothendieckTopology.Point.sheafFiber
  in Mathlib.CategoryTheory.Sites.Point.Basic, specialized at
  AlgebraicGeometry.Scheme.pointSmallEtale in Mathlib.AlgebraicGeometry.Sites.EtalePoint.
  The fibre is the colimit over the opposite category of pointed etale neighbourhoods.
- Proof dependencies are imported: Mathlib.Algebra.Homology.DerivedCategory.Fractions
  (both calculus-of-fractions instances), the derived-category basic and homology
  modules through the public derived-category dependency,
  WeilConjectures.AlgebraicGeometry.EtaleSheaves (the recorded sheaf-category module),
  and WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
  (AlgebraicGeometry.Scheme.isIso_of_isIso_sheafFiber_map).

Edge cases: the empty scheme has no geometric points; its sheaf category and
its derived category are trivial, so the criterion remains valid. Zero objects,
zero morphisms between zero objects, and identity morphisms are included.
There is no lower bound fixed uniformly on all K and L, no assumption on
characteristic, finite type, separation, torsion, constructibility, or stalk size.
Quantification over all integer degrees includes negative degrees and degree zero.

Searches made:

- msearch.py leanfinder: "A morphism in the bounded below derived category of
  etale abelian sheaves is an isomorphism if and only if every geometric stalk
  of every cohomology map is an isomorphism". Eight hits, chiefly
  TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso and other general sheaf criteria;
  none states this derived etale criterion.
- msearch.py loogle: "DerivedCategory.isIso_iff, Scheme.pointSmallEtale, sheafFiber".
  Zero hits; unknown identifier Scheme.pointSmallEtale.
- msearch.py grep: "isIso.*sheafFiber.*homology|sheafFiber.*homology". Zero Mathlib hits.
- rg on upstream WeilConjectures and project lean/Sheaf for
  `isIso.*homology|homology.*isIso|stalk.*conserv|derived.*[Ss]talk`, and the prescribed
  upstream grep for this blueprint id, found
  WeilConjectures.AlgebraicGeometry.Sites.DerivedStalk.
  Read its complete declarations and proof. The existing theorem
  AlgebraicGeometry.Scheme.isIso_iff_isIso_sheafFiber_map_homologyFunctor_map_plus
  is generic in the coefficient category and tests only the canonical family
  `S.uliftPointSmallEtale s`, indexed by scheme points s. This delivery uses the
  node's precise abelian coefficient category and explicitly tests every geometric
  point `Spec Ω → T`; it introduces no duplicate definition. The existing theorem
  is related but does not literally state that all-geometric-points formulation.
- rg for `derived_stalk|isIso_iff_isIso_geometricStalk` throughout Mathlib,
  upstream WeilConjectures and lean/Sheaf found no declaration with the new name.

Validation: scompile.py NG lem-weil-pbc-derived-stalk-conservative on the module
passed initially in 1.5 seconds, nice 19, two threads, 60-second limit, with no warnings
or errors. Delivery dry run follows; the second reader supplies the independent
second-reading section and performs delivery.

Final signature uses IsAlgClosed, as required by the project geometric-point convention;
Mathlib derives IsSepClosed for the pointSmallEtale construction.


## Second reading by NG

Read independently against the complete DAG node and its blueprint source
sec-curve-estimates/sk-prop-cd/lem-weil-pbc-derived-stalk-conservative.md,
with Stacks derived.tex Tags 05RT (lemma-acyclic) and 05RU
(definition-unbounded-derived-category), including the surrounding abelian-category
hypothesis. Read both statement dependency nodes and their actual declarations.
No source-wide scheme hypothesis is omitted.

Object, hypothesis and conclusion checklist (all pass):

- Arbitrary scheme T: `{T : Scheme.{u}}`; no separation, finiteness,
  characteristic, nonemptiness or Noetherian hypothesis.
- K and L in D⁺(T_et): `DerivedCategory.Plus (Sheaf T.smallEtaleTopology
  AddCommGrpCat.{u + 1})`. The dependency module DerivedCategories explicitly
  specifies this abelian coefficient category for notation without a ring.
  Mathlib TStructure defines Plus as the full subcategory for the standard
  t-structure; this is cohomological boundedness below, with no common bound.
- Arbitrary morphism K → L: `(f : K ⟶ L)` includes derived roofs, as required
  by the node proof; no selected representatives or chain-map restriction.
- Isomorphism in D⁺ and equivalence: `IsIso f ↔` has exactly both directions.
- Every geometric point: `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
  (t : Spec (CommRingCat.of Ω) ⟶ T)`. Read the scheme-conventions source:
  geometric points use algebraically closed fields. Mathlib pointSmallEtale
  accepts their inferred separable closedness, and its fibre consists precisely
  of lifts to etale neighbourhoods.
- Every integer i: `(i : ℤ)`, after the geometric-point binders; no degree
  restriction or positivity premise.
- The map of cohomology sheaves: `(DerivedCategory.Plus.homologyFunctor _ i).map f`.
  Read Plus.lean: this functor is inclusion followed by derived homology.
- Its stalk map and its invertibility: `(pointSmallEtale t).sheafFiber.map`
  of that map inside `IsIso`. Read Point/Basic: presheafFiber is the colimit
  over the opposite category of fibre elements, and sheafFiber restricts it
  to sheaves. Thus these are precisely stalks of the cohomology sheaves;
  no exactness or stalk-complex comparison is an added assumption.

Edge cases pass: the empty scheme has no such geometric points and its
abelian sheaf category, hence derived category, is trivial. Zero objects and
maps between them are included. Negative degrees and i = 0 are included.
All characteristics are allowed. There is no index set whose nonemptiness
is assumed. The universe u is arbitrary; fields in Type u include algebraic
closures of residue fields of Scheme.{u}. The coefficient universe u+1 is
the recorded project encoding, not an extra bound or small-field hypothesis.
All variables and the sole universe are explicitly bound.

Independent searches: msearch leanfinder query "Isomorphisms of bounded below
derived etale sheaves detected by cohomology at algebraically closed field
valued points" returned eight unrelated ring-etale hits. Loogle query
"DerivedCategory.Plus.isIso_iff" returned the general cohomology criterion,
whose signature was checked: it has no stalk clause. The msearch grep query
"sheafFiber.*homologyFunctor|homologyFunctor.*sheafFiber" returned zero hits.
Direct rg over Mathlib derived-category modules, project lean/Sheaf and
upstream WeilConjectures, using isIso/homology/stalk/conservative terms,
found the upstream Sites/DerivedStalk module. Read it in full: its Plus
criterion tests `(S.uliftPointSmallEtale s)` for `s : S`, not every
`Spec Ω → S`. Specializing its coefficient category does not change that
quantifier into this node's all-geometric-points statement. A comparison or
additional argument is required; it is not the exact existing declaration.
Retaining this module adds no new definition or duplicate notion.

H5/H6/H8/H9 pass: no definitions or instances are introduced; the only proof
is sorry; the docstring covers fullness, the localization/roof argument,
sheaf conservativity and functoriality of inverses, with the node sources.
No new nodes, dependency modules or statement correction are present, so
H12/H13 and correction-citer review do not apply.

The only mismatch found was bookkeeping: lean.statement had normalized
whitespace rather than the signature verbatim. Replaced it with the exact
multiline signature extracted from the file. No Lean or mathematical statement
was changed. Server validation uses only scompile.py with the mandated
nice 19, two threads and 60 seconds per file.
