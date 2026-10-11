## Worker report

The module states `CochainComplex.affine_perfect_hom_colimit`. It introduces a filtered
index category `I`, a commutative ring `A`, the derived category `D(A)`, a diagram `H` of
stage Hom data, and a canonical map from its colimit to a derived Hom type; the conclusion
is that this map is bijective. The proof is `sorry`, as required for stage 2. The docstring
records the three affine proof steps: ordinary Hom complexes, finite-presentation descent,
and passage from cycles and boundaries to zeroth cohomology.

The dependency declarations read were `AlgebraicGeometry.schemeDerivedCategory` in
`Sheaf.AlgebraicGeometry.DerivedCategory` and `AlgebraicGeometry.Scheme.IsPerfect` in
`Sheaf.AlgebraicGeometry.PerfectComplex`; these are scheme-level notions and do not provide
a ring-level Hom-colimit declaration. The abstract derived category is Mathlib's
`DerivedCategory`.

Edge cases checked: `I` is allowed to be empty only subject to `IsFiltered`; no finite or
nonzero assumption is added on the ring or Hom types; universes of `I`, `A`, and the
morphism universe are explicit.

Searches: LeanSearch for filtered-colimit Hom from bounded finite-projective complexes was
unavailable; LeanFinder returned only generic projective/K-projective declarations; Loogle
for `ModuleCat.extensionOfScalars` returned no hits; grep in Mathlib homology found no
Hom-colimit theorem. Project grep found no existing declaration of this node.

Initial encoding fault (resolved below): the imported node's prose names a concrete filtered system of rings and
bounded finite-projective scalar extensions, while the available project declarations do
not expose a single Lean encoding of those varying derived categories. The statement uses
an explicit diagram `H` and canonical map to make the claim typeable; this was an incorrect encoding and has been replaced in the second reading.

## Earlier second reading (a previous round; superseded)

The module and node were reread together; the declaration compiles and the recorded signature matches the file. A second independent reader should verify the affine encoding against Tag 09RE before landing.


## Second reading by J1

Independent second reading, with the node, both dependency declarations, and Stacks
`perfect.tex` open. The repository has no literature checkout; the local obtained source
`/home/ubuntu/c1-stacks-review/perfect.tex`, lines 7222–7311, contains Situation
`situation-descent` and the Tag 09RE proof `lemma-descend-homomorphisms`.
The mathematical statement of the item is unchanged. The first worker's statement was
false: arbitrary `H`, `E`, `K`, and `canonical` need not give a bijection. This was H3,
not a defect of the mathematical node. That encoding and its unresolved dispute are gone.

Object/hypothesis/conclusion checklist:

- Directed filtered ring system: `I : Type u`, `[Preorder I]`,
  `[IsDirected I (· ≤ ·)]`, `F : I ⥤ CommRingCat.{u}`. PASS: the source uses a
  directed system, and the node proof explicitly uses a filtered preorder.
- Colimit ring A: `[HasColimit F]`, `colimit F : CommRingCat.{u}`. PASS: no
  separate arbitrary ring or map. Every structure map is `colimit.ι F i`.
- Fixed stage A₀: `i₀ : I` and `F.obj i₀`. PASS. The tail is `Set.Ici i₀`.
- E₀ and K₀: `CochainComplex (ModuleCat.{u} (F.obj i₀)) ℤ`. PASS: actual
  module complexes, rather than arbitrary derived objects.
- Boundedness of each: the first conjunct of `hE` / `hK` gives integers `a,b`
  and `IsZero` outside them. PASS: arbitrary integer bounds; no common bound imposed.
- Finite projectivity of each term: `Module.Finite` and `Module.Projective` in
  the second conjunct of `hE` / `hK`. PASS: finite projective, not finite free,
  and no assumption on the ring. On a commutative ring this is exactly a direct
  summand of a finite free module.
- Stage Eᵢ,Kᵢ: `ModuleCat.extendScalars (F.map (homOfLE i.property)).hom`
  followed by `.mapHomologicalComplex (.up ℤ)` on E₀,K₀. PASS: termwise tensor.
- Limit E,K: the same construction with `(colimit.ι F i₀).hom`. PASS.
- D(Aᵢ), D(A): `DerivedCategory` of the indicated `ModuleCat`, with explicit
  `HasDerivedCategory.{w}` choices. PASS: localization at quasi-isomorphisms.
  Opened `schemeDerivedCategory` and `Scheme.IsPerfect`: they encode schemes and
  sheaves, not rings. Their affine forms are the generic Mathlib localization and
  finite-projective term conditions above, not a replacement scheme-level definition.
- Actual stage Hom diagram: `ident i` is an equivalence from `H.obj i` to the
  indicated derived Hom set. `htransition` fixes the transition on every chain-map
  representative to `DerivedCategory.Q.map (scalarExtensionHom …)`. PASS:
  bounded projective sources represent every derived morphism by a chain map, so
  these equations determine the entire transition, without assuming the conclusion.
- Canonical comparison: `c : Cocone H`, `e` identifies its vertex with the limit
  derived Hom set, and `hcanonical` fixes each leg on all chain representatives.
  PASS: `e ∘ colimit.desc H c` is exactly the canonical comparison. These binders
  present the specified diagram and cocone; they do not assert surjectivity or
  injectivity. They can be supplied by the usual derived scalar extensions.
- Isomorphism: `Function.Bijective (e ∘ colimit.desc H c)`. PASS: an isomorphism
  of Hom sets; the canonical comparison is additive as well, so this is equivalent
  to the node's Hom-group isomorphism. No additional conclusion is asserted.

Source-wide assumptions: Situation 36.29 assumes qcqs schemes and affine transitions.
In this ring-only affine specialization, every spectrum is qcqs and every ring-induced
transition is affine; no additional assumption is needed. The source's more general
K-flat target is specialized by the node to bounded finite-projective K₀, which is K-flat.
No node correction is needed.

Edge cases: the source fixes a stage, so the empty index set is already excluded by
`i₀ : I`; the tail contains i₀ and is directed. Preorders need not be antisymmetric.
The zero ring, zero complexes, and empty affine scheme are included. Bounds need not
straddle zero, and degree zero is treated identically to every integer degree. No
characteristic or domain assumption occurs. Index and rings have universe u, as the
project convention requires; finite modules can be represented in the same universe.
Derived morphisms and H have arbitrary universe w, and all universe variables are bound.

Independent searches: Loogle `ModuleCat.extendScalarsComp` and
`CategoryTheory.NatIso.mapHomologicalComplex` find the canonical existing components.
LeanFinder `morphisms in derived category scalar extension bounded complexes finite
projective filtered direct limit` returns generic Ext and derived-functor declarations,
not this lemma. LeanFinder's transported-chain-map query returns shape-extension maps
and the single-extension module map, not our comparison. LeanSearch's canonical
scalar-extension query is unavailable (Internal Server Error). Grep for
`scalarExtensionHom|baseChangeHom|extendScalarsComp` in Mathlib homology, upstream
WeilConjectures, and project Lean finds no exact theorem or transported chain-map
function. DAG grep and `blueprint_refs.py search 'scalar extension'` find the general
scalar-extension node, which is cited rather than recreated. Opened its
`ringExtendScalars` and `ringExtensionComp` signatures: arbitrary-ring left adjoints and
their canonical comparison. For commutative rings, Mathlib's `extendScalarsComp` is
that same unique-adjoint comparison, not a new scalar-extension notion.

Repairs: replaced the arbitrary-map theorem by the full ring/complex/canonical-map
statement; added the transported-chain-map definition node and module to express the
canonical maps without hidden `let`, `show`, local notation, or hollow data; expanded
the proof docstring to all three DAG steps; removed duplicate and unused imports.
There are no dependency replacement modules and no statement_change. The new node is
read against the affine source: it only names the canonical map implicitly used there,
not a new hypothesis. Its DAG fields and searches follow brief §5. Its definition is
an explicit composition of existing scalar-extension maps, comparison isomorphisms,
and equality transports; no data or proof is `sorry`. The item's only theorem has
proof `sorry`, as stage 2 requires. Signatures are recorded verbatim in the node copies.

## New nodes

`def-pc-complex-scalar-extension-hom` names scalar extension of a chain map between two
complexes extended from a common base ring, transported by canonical associativity.
Source: Tag 09RE's affine proof. Its dependency notions already exist as
`def-pc-cochain-complex-modules` and `def-pod-ring-scalar-extension`; neither provides
this transported map. Mathlib supplies all construction components but no declaration
of the complete map. The three independent search kinds and the DAG search are recorded
above and in the new node. The definition has no sorry and introduces no stronger notion.
