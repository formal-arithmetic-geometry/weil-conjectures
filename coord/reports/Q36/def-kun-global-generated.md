## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleGloballyGenerated` defines the canonical
all-global-sections evaluation morphism and the predicate that it is epi, for module-valued
étale sheaves and explicitly for abelian étale sheaves. All four declarations are definitions
with real data; no theorem or `sorry` is introduced. The node is unchanged except for `lean`.

I read the item, both statement dependencies and their full Lean records, Mathlib's
`constantSheaf`, `constantSheafAdj` and `Functor.mapHomologicalComplex` declarations and
docstrings, and the current server source of the recorded
`WeilConjectures.AlgebraicGeometry.EtaleSheaves` module. The blueprint source was also read on
the server because the local read-only literature tree does not contain its Markdown files;
it agrees verbatim with the node.

Clause-by-clause correspondence:

- "Let T be a scheme": `{T : Scheme.{u}}`, with `universe u` explicitly declared.
- The coefficients and the sheaf of Λ_T-modules on T_et: `{Λ : Type (u + 1)} [CommRing Λ]`
  and `F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`, the project-approved
  module-valued encoding from the `def-weil-pbc-etale-sheaves` record. No Noetherian,
  connectedness, finite-type, nonzero-ring or finiteness assumptions are imposed.
- All global sections are exactly `F.obj.obj (op (Etale.mk (𝟙 T)))`. The actual identity
  étale object is used, with `MorphismProperty.Over.mkIdTerminal` as its terminal proof.
- The source direct sum is modeled by
  `(constantSheaf T.smallEtaleTopology (ModuleCat Λ)).obj
  (ModuleCat.of Λ (F.obj.obj (op (Etale.mk (𝟙 T))) →₀ Λ))`.
  Here `I →₀ Λ` is the free module, hence the coproduct of copies of Λ indexed by I.
  Mathlib's `constantSheafAdj` makes the constant-sheaf functor a left adjoint, so it
  preserves that coproduct. Thus this is precisely a concrete coproduct model of the
  displayed direct sum of constant coefficient sheaves, with no choices of arbitrary
  maps or extra universal-property assumptions. Using this model avoids expensive
  instance search for the independently chosen categorical coproduct of sheaves.
- `etaleGlobalSectionsEvaluation F` is the adjoint of
  `ModuleCat.ofHom (Finsupp.linearCombination Λ id)`. On a basis vector
  `Finsupp.single s 1`, `Finsupp.linearCombination_single` gives `1 • s = s`.
  Under the constant-sheaf adjunction this specifies exactly the map `1_s ↦ s`.
  On any étale object the section is restricted along its unique map to the identity
  object, as specified by `constantPresheafAdj` and the sheafification adjunction.
- "Globally generated if this morphism is an epimorphism of sheaves" is exactly
  `IsGloballyGeneratedEtaleSheaf F := Epi (etaleGlobalSectionsEvaluation F)`.
- The geometric-stalk criterion is explicitly deferred in the source to the properties
  of this notion; no equivalence theorem is part of this definition or this delivery.
- "For abelian sheaves take Λ = ℤ": `etaleAbelianGlobalSectionsEvaluation` takes
  `F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}` and uses the constant sheaf
  of `F.obj.obj (op (Etale.mk (𝟙 T))) →₀ ℤ`, with adjoint map
  `(Finsupp.linearCombination ℤ id).toAddMonoidHom`.
  This is the same integer-module construction expressed directly in abelian groups.
  `IsGloballyGeneratedAbelianEtaleSheaf F` is its `Epi` predicate. This direct encoding
  avoids trying to force the small type ℤ itself to inhabit `Type (u + 1)` and is
  available to the downstream abelian-sheaf statements without any coefficient lift.

Dependency declarations used:

- `def-kun-constant-sheaf`: the record's specialization to
  `CategoryTheory.constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`, whose
  actual definition is in `Mathlib.CategoryTheory.Sites.ConstantSheaf` and is imported.
  It is sheafification of the constant presheaf, and `constantSheafAdj` is its
  adjunction to sections at the terminal object. The recorded primary
  `Functor.mapHomologicalComplex` in `Mathlib.Algebra.Homology.Additive` is the
  termwise-complex component of that mixed dependency record; the present item uses
  its underlying constant-sheaf component, not complexes. No duplicate is introduced.
- `def-weil-pbc-etale-sheaves`: the record explicitly permits both `Sheaf` with
  `ModuleCat` coefficients and `Sheaf` with `AddCommGrpCat` coefficients. Its recorded
  module `WeilConjectures.AlgebraicGeometry.EtaleSheaves` is publicly imported, using
  the canonical Mathlib categories and the supplied sheafification infrastructure.
- Mathlib's `Finsupp.linearCombination` from
  `Mathlib.LinearAlgebra.Finsupp.LinearCombination` is the actual evaluation linear map.
  `Mathlib.Algebra.Category.ModuleCat.AB` supplies the coefficient category's
  Grothendieck abelian instance needed for the existing sheafification construction.

Edge cases checked before writing and against the final definitions:

- The zero sheaf has its zero global section; the evaluation target is zero and its map
  is epi. No nonzero-section restriction changes the indexing type.
- For an empty scheme every étale sheaf has only the zero section; the construction
  still makes sense and gives the expected epi to the zero sheaf.
- The zero coefficient ring is allowed; its module sheaves are zero. No `Nontrivial`
  instance occurs. The integer version also allows arbitrary torsion and nontorsion
  abelian sheaves.
- Infinite section sets are allowed: finitely supported coefficients describe an
  arbitrary direct sum, not a finite sum or a product.
- The empty indexing family is correctly represented by the zero free module, though
  the global-section set of a module sheaf itself is inhabited by zero.
- The scheme universe is arbitrary, and the sheaf-value universe is the established
  `u + 1` convention. No equality of the site's object and morphism universes is assumed.

Searches for reuse and for name collisions (2026-10-16):

- `msearch.py ... leanfinder`: "A sheaf of modules is globally generated if the evaluation
  map from the coproduct of copies of the constant coefficient sheaf indexed by global
  sections is an epimorphism". Eight related hits for
  `SheafOfModules.GeneratingSections` and its epi constructions, none for this exact
  all-global-sections evaluation predicate.
- `msearch.py ... loogle`: `"constantSheafAdj", "ModuleCat"`: zero hits. The local
  `constantSheafAdj` source was then read in full and used directly.
- `msearch.py ... grep`: `IsGloballyGenerated|globalEvaluation|GloballyGenerated` in
  Mathlib's `Algebra/Category/ModuleCat`: zero hits.
- `msearch.py ... leansearch`: "A sheaf is globally generated when the evaluation
  morphism indexed by all global sections is an epimorphism": service unavailable,
  Internal Server Error; the other searches and source reads supplied the evidence.
- `rg` in the upstream `WeilConjectures` and project `lean/Sheaf` trees for globally
  generated/evaluation terminology found generic evaluation and free-sheaf infrastructure,
  not the item. `rg` for `def-kun-global-generated` in upstream found no declaration.
- `rg` for each of the four delivered declaration names in Mathlib, upstream,
  `dag/lean_names_upstream.json` and the project's `lean/Sheaf` found no collision.
- Read Mathlib `SheafOfModules.free`, `freeHomEquiv` and related free-section lemmas:
  these would provide an alternative over the other module-sheaf encoding, but the
  existing project convention for this chapter uses ModuleCat-valued sheaves.

Validation: the final module passed `scompile.py` in both sandbox and library-path modes
without errors or warnings (11.1 s and 9.2 s). Earlier drafts diagnosed slow coproduct
instance search; the final constant-free-module construction needs no new instances,
extra hypotheses, timeout changes, helper nodes or dependency repairs.
No statement dispute or source correction is needed. The independent second reader
will write the second-reading section and perform delivery.

## Second reading by Q36

I opened the node copy at `dag/nodes/sec-smooth-purity/def-kun-global-generated.json`,
the complete module `Sheaf/AlgebraicGeometry/EtaleGloballyGenerated.lean`, and the two
statement dependencies. The source place is blueprint `def-kun-global-generated`, order
1691, in `sk-prop-sf-kunneth-ordinary`. The item is a definition, so `proof` and
`proof_deps` are empty; the sentence mentioning geometric stalks is a pointer to the
separate stalkwise lemma and is not asserted here.

The node's objects, hypotheses, and clauses match the Lean as follows.

- A scheme \(T\) is the implicit `{T : Scheme.{u}}` parameter of all four definitions.
- A commutative coefficient ring Λ is `{Λ : Type (u + 1)} [CommRing Λ]`; this is the
  established `ModuleCat.{u + 1} Λ` convention of `def-weil-pbc-etale-sheaves`, with no
  noetherian, connectedness, finiteness, nonzero-ring, or characteristic assumption.
- A sheaf \(F\) of Λ-modules on the small étale site is
  `F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`. The global sections indexing
  type is exactly `F.obj.obj (op (Etale.mk (𝟙 T)))`, the value at the terminal étale
  object.
- The displayed direct sum of constant copies of Λ is represented by
  `(constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
  (ModuleCat.of Λ (sections →₀ Λ))`, where `sections` is the preceding global-section
  type. `constantSheafAdj` is the canonical left adjoint to terminal-object sections,
  and `sections →₀ Λ` is the free Λ-module (the coproduct of copies of Λ), so this is
  the canonical coproduct model rather than an arbitrary source object.
- `etaleGlobalSectionsEvaluation F` is the adjoint of
  `ModuleCat.ofHom (Finsupp.linearCombination Λ id)`. Thus the basis vector indexed by
  \(s\) maps to \(s\), exactly the node's `1_s ↦ s` clause, and the adjunction gives the
  corresponding sheaf morphism.
- “Globally generated” is rendered by
  `IsGloballyGeneratedEtaleSheaf F := Epi (etaleGlobalSectionsEvaluation F)`, exactly
  the asserted epimorphism condition.
- The abelian specialization Λ = ℤ is rendered independently as
  `etaleAbelianGlobalSectionsEvaluation` on
  `Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}`, using the free abelian group
  `sections →₀ ℤ` and the additive map from `Finsupp.linearCombination ℤ id`; its
  predicate is `IsGloballyGeneratedAbelianEtaleSheaf`. This preserves the node's
  integer-coefficient clause without adding a characteristic or torsion hypothesis.

Both dependency records were opened. `def-kun-constant-sheaf` supplies the constant
sheaf notion, and `def-weil-pbc-etale-sheaves` supplies the small étale sheaf/module
encoding; neither is duplicated. The Lean `statement` field is byte-for-byte the
signature of `IsGloballyGeneratedEtaleSheaf`, from `def` through `Prop`. No variables or
universes are left implicit beyond the declared `u`, and the module compiled with
`scompile.py` without errors or warnings.

Edge cases were checked against the definitions: the zero sheaf has a singleton global
section type and the resulting zero map to the zero sheaf is epi; an empty scheme is
covered because no nonemptiness assumption is present; the zero coefficient ring is
allowed; empty indexing is represented by the zero finitely-supported module; infinite
global-section sets are allowed; and arbitrary scheme and coefficient universes are
retained. The abelian case allows arbitrary abelian sheaves, including torsion and zero
objects. No \(n=0\) parameter occurs in this definition.

For the H4 duplicate check I ran `msearch.py` LeanFinder, Loogle, and grep searches for
the all-global-sections evaluation/global-generation notion, and searched both the
upstream `WeilConjectures` tree and this project's `lean/Sheaf` tree. Mathlib's
`SheafOfModules.GeneratingSections` and `freeHomEquiv` are only generic arbitrary-family
infrastructure; no declaration has the canonical all-global-sections étale statement.
The source and DAG searches likewise found no exact declaration, so retaining a new
module is correct. The only report correction was editorial: the zero-sheaf description
was made precise as a singleton index set, and the field example was qualified; no Lean
statement, dependency, or node field was changed. There are no new definition or
dependency modules and no statement correction.
