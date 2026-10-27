## Worker report

The module `Sheaf.CategoryTheory.DerivedColimitScalarCoherence` states the node in seven
named theorem clauses, each with `sorry` and a source/proof docstring. All helper data
are actual constructions from Mathlib adjunctions, exact-functor descent, and identities
on underlying sections. There is no choice of data from an existence assertion.

Hypothesis and clause correspondence:

- Small identity-cover sites E,D: `{E D : Type u} [SmallCategory E] [SmallCategory D]`
  and the ordinary functor categories `Eᵒᵖ ⥤ ModuleCat.{u} R`. This is precisely the
  all-presheaves presentation of the bottom Grothendieck topology used by the bar node.
- Four commutative rings: four explicit `Type u` binders and `CommRing` instances;
  `φ, ψ, a, b` are the four ring homomorphisms. `hab : b.comp φ = ψ.comp a` is the
  coefficient-square hypothesis. The indexing functor is `u : E ⥤ D`.
- Derived colimits and exact constants: `B : CategoryColimitBarSystem.{u}`, with
  `(B.models E R).derived` and `.adjunction`, and the analogous three other models.
  Their localizations are the bar dependency's ordinary unbounded derived categories
  in Hom universe u+1. No bounded-above subcategory is substituted.
- Derived extension and tensor/restriction adjunctions: `T, T', T₀, T₀'` with
  `adjT, adjT', adjT₀, adjT₀'`. These are presentations of the stipulated left
  adjoints to the actual termwise restrictions. Quantification over a left-adjoint
  presentation is harmless: its unique unit-compatible isomorphism is exactly the
  equivalence relation used in this node. It does not assume an extra property of
  the ring map or an arbitrary natural comparison. The canonical cochain comparison
  is defined from the ordinary unit, so the representative assertion fixes its
  normalization too, even for a different presentation of the derived left adjoint.
- Termwise precomposition/scalar restriction: `categoryScalarPrecomp u a` is Mathlib
  whiskering-left by `u.op` followed by Mathlib whiskering-right by restriction.
  `categoryScalarPointSquare`, `categoryScalarConstantSquare`, and
  `categoryScalarPresheafSquare` identify the right adjoints by the identity on
  underlying elements. `categoryScalarDerivedSquare` descends exactly those
  identifications with `mapDerivedCategoryCompIso` inserted; no noncanonical
  natural isomorphism is a hypothesis.
- The unit-normalized isomorphisms χ: `categoryScalarExchange` is
  `conjugateIsoEquiv` applied to the two composite adjunctions and the actual
  constant/restriction identification. Its inverse Hom construction is precisely
  the specified composite-unit normalization and gives an isomorphism, uniquely.
- Arbitrary derived M,M',t: the main theorem's last binders are those objects and
  `t : M ⟶ (categoryScalarPrecomp u a).mapDerivedCategory.obj M'`. There is no
  assumption that t has a chain representative.
- a_R: the inner `scalarAdjointMap (B.models E R).adjunction
  (B.models D R').adjunction ... t` on the right. The definition is inverse
  transposition of t followed by the target colimit unit and the canonical
  right-adjoint square.
- t_S: the inner `scalarAdjointMap adjT adjT' ... t` on the left, using the
  coefficient square with precomposition.
- a_S: the outer colimit `scalarAdjointMap` on the left, applied to t_S.
- b_R: the outer `scalarAdjointMap adjT₀ adjT₀' ...` on the right, applied to a_R.
- The asserted derived equality: `categoryColimitScalarCoherence` states
  `a_S ≫ Res_b.map χ_D = χ_E ≫ b_R`, in Mathlib's left-to-right convention.
- Identity maps: `scalarAdjointMap_identity` applies to each colimit/coefficient
  transpose; the right-adjoint identity square has the canonical unitors.
- Composition of indexing functors: `scalarAdjointMap_composition` gives the
  formula for input `t ≫ P.map t'` and the two semilinear output arrows.
  `scalarAdjointSquareVComp` explicitly inserts every associator. Applying it to
  descended reindexing functors uses their canonical exact-derived composition iso.
- Pasting coefficient squares: `scalarAdjointMap_coefficient_pasting` is the
  horizontal-pasting formula under `Adjunction.comp`, with the right square
  `scalarAdjointSquareHComp`. Together with vertical pasting and the conjugate
  unit equation, this is the identity/composition/pasting clause for the exchanges.
- Ordinary presheaves F,G and semilinear natural t: `bar_square` has exactly these
  binders, with `t : F ⟶ u.op ⋙ G ⋙ ModuleCat.restrictScalars a`.
- Chain isomorphisms Φ: `barIso` asserts existence for every F, without flatness;
  its formula specifies `(σ,s⊗x) ↦ s⊗(σ,x)`. Mathlib puts the coefficient first,
  symmetrically to the source notation. `bar_square` quantifies over the two
  isomorphisms satisfying precisely those formulas, so it applies to any of their
  presentations rather than choosing one from a postponed existence theorem.
- The tensor arrows: `bar_square` supplies tS and kS with the explicit formulas
  `s⊗x ↦ b(s)⊗t(x)` and `s⊗x ↦ b(s)⊗B.map(u,a,t)(x)` in every degree.
  Its final equation is equality of actual complex morphisms, not cohomology maps.
  Inserting `B.formula` gives the common generator `(uσ,t(x))⊗b(s)` stated by the node.
- No flatness at chain level: neither `barIso` nor `bar_square` has hF/hG or a
  flatness hypothesis. For comparison, the already landed downstream
  `categoryColimitChangeRings_bar_naturality` requires objectwise flatness and is
  not an exact existing match for this node.
- K-flat derived representatives: `bar_represents` has hF and hK on precisely
  F[0] and K_E,R(F), using the recorded ordinary-category `MorphismProperty.kFlat`.
  Its first two conjuncts assert invertibility of the canonical comparisons.
  Its equality identifies Q(Φ) with χ through the exact single-complex transport,
  bar `.model`, and the two canonical cochain comparisons. The normalized
  adjunct definition of these comparisons uses the ordinary unit x↦1⊗x;
  therefore the same formula identifies the tensor arrows with the derived
  transposes. The proof docstring spells out that identification at both ends.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.DerivedColimitBar`: `CategoryColimitBarSystem`,
  `CategoryColimitBarModel.derived`, `.adjunction`, `.bar`, `.generator`, `.model`,
  `.transpose`, `.colimitAugmentation`, and the semilinear `.map`/`.formula` fields.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, the general sheaf notion. In the explicitly
  permitted ordinary-presheaf presentation its restriction is sectionwise
  `ModuleCat.restrictScalars`, composed by Mathlib whiskering. No new restriction
  operation replaces it.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`:
  `ModuleCat.OrdinaryDerivedChangeOfRings`, the universal counit/computation
  clauses and `ordinaryDerivedExtendScalars`; also its publicly retained generic
  `SheafOfModules.DerivedChangeOfRingsCochainModel`.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction`, read with its unit and
  adjunct normalizations. The statement uses the same adjunction data in the
  ordinary-presheaf presentation, with cochain comparisons defined by that unit.
- `Mathlib.CategoryTheory.Adjunction.Basic`: `Adjunction.comp` and
  `Adjunction.comp_unit_app`; `Mathlib.CategoryTheory.Adjunction.Mates`:
  `conjugateIsoEquiv`, `unit_conjugateEquiv_symm`, `mateEquiv_vcomp`,
  `mateEquiv_hcomp` (proof plan). No duplicate conjugation is defined.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`: publicly exposed
  `CategoryTheory.MorphismProperty.kFlat`, as explicitly authorized by its
  recorded ordinary-category interface. This is the total-tensor K-flat predicate.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: existing
  tensor convention; ordinary module tensors are `ModuleCat.extendScalars` and
  Mathlib's monoidal functor-category/cochain structures. The helper instance
  `categoryScalarPresheafClosed` is the existing
  `Functor.functorCategoryMonoidalClosed`, supplying the standard cochain tensor
  instances; it does not construct a second tensor operation.

Dependency/import cycle audit: `lem-trf-derived-colimit-change-rings` is a consumer
of this item through `proof_deps`. Its landed module contains a useful helper
record but importing it here would create a cycle when proof imports are wired.
The final file does not import it or add it to stmt_deps; it uses actual functors,
Mathlib adjunctions, and the already recorded bar interfaces directly. The two
proof-only nodes `lem-trf-objectwise-flat-bar-kflat` and
`lem-trf-bar-scalar-unit-transpose` currently have no Lean record/module to import;
their argument is reproduced in the relevant theorem's proof docstring, and their
DAG proof dependencies remain unchanged. No new definition node or dependency
repair is needed: all helpers expand maps in this item's statement and are
listed in lean.declarations.

Edge cases checked before writing: empty E or D (no Nonempty hypothesis;
bar generators and zero colimits behave as specified), the zero ring (no
Nontrivial hypothesis), the one-object identity category, φ=identity,
identity u and t, composition of two indexing functors, degree zero and all
positive zero degrees, nonflat Z→Z/2 with torsion F (chain square retained),
and unbounded derived M with a morphism not represented by a direct chain map.
Independent category universes and localization universes are explicitly bound
in generic helpers; concrete sites, rings and module sizes follow the bar
system's single size universe u and its derived Hom universe u+1.

Searches (2026-10-24):

- `msearch.py ... leanfinder "Unit normalized derived colimit extension of scalars
  exchange is natural for semilinear maps and commutative ring squares"`: 8 hits,
  ordinary ModuleCat scalar-extension associators and composition Hom formulas.
  No derived semilinear bar comparison.
- `msearch.py ... loogle "CategoryTheory.conjugateIsoEquiv,
  CategoryTheory.Adjunction.comp"`: 0 hits.
- `msearch.py ... grep "derived.?colimit.*scalar|bar.*naturality|conjugateIsoEquiv"`:
  25 hits, mostly generic conjugate-isomorphism uses and definitions; no exact item.
- `msearch.py ... leansearch "derived colimit exchange extension of scalars
  semilinear naturality bar complex"`: 8 hits, ordinary scalar restriction
  colimits/extension Hom equivalence and group bar formulas; none states this node.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, Mathlib and
  `dag/lean_names_upstream.json` for `categoryColimitScalarCoherence`,
  `scalarAdjointMap`, `categoryScalarExchange`, `categoryScalarPointSquare`,
  `scalarAdjointSquareVComp`: no name collision. Search by the item id in
  `lean/WeilConjectures` and `lean/Sheaf`: no existing declaration.
- Concept search `scalar.*[Cc]oherence|[Cc]olimit.*[Ss]calar|[Bb]ar.*[Tt]ensor` in both
  project roots found generic scalar-coherence work and the downstream
  `DerivedColimitChangeRings` module, read in full. Its bounded-above comparison
  and flat-only bar naturality do not state this item's arbitrary unbounded
  derived t plus chain square without flatness.

Sources read: `literature/stacks-project/sites-cohomology.tex`,
`example-morphism-categories` (08PH, lines 10117ff) and `lemma-change-of-rings`
(08Q8, lines 10209ff), including the source's order/left-right typo already
noted by the node. The current unit metadata `dag/units/sk-i-curve-zero.json`
was checked; this item is an auxiliary node, not that unit's own statement.
No statement correction or dispute is asserted.

Validation: single-file `scompile.py N9 lem-trf-derived-colimit-scalar-coherence`
used for every compiler run. Seven named theorems are postponed; definitions
and instances have real terms. No local/global build, direct git command,
shared-repository write, or launcher-script edit was performed.

## Second reading by N9

This is a second reading by the same dispatcher worker, not an assertion of an
independent worker review: the prompt prohibits starting other agents and says
that the maintainer independently reviews the delivery. I reread the node and
file together after the first compiling version. Found and repaired:

1. The tempting `DerivedColimitChangeRings` import pointed to a consumer whose
   proof_deps names this item. Removed it, expressed all sectionwise functors
   with Mathlib whiskering, and used directly specified left adjoints. No
   downstream existence theorem is used to construct these maps.
2. The first chain comparison reused a flat-only interface. Replaced it with
   the explicit barIso existence and formula for every F, plus bar_square for
   arbitrary F,G; flatness remains only in the conditional K-flat comparison.
3. The K-flat predicate needed the standard tensor of presheaf complexes.
   Supplied the existing Mathlib closed structure as an instance; did not
   assume a tensor structure or impose a universe equality.
4. Exact restrictions on derived categories commute up to the canonical
   descent isomorphism, not definitionally. Each right-adjoint square now
   contains `mapDerivedCategoryCompIso`, the actual ordinary identity, and
   the other composition comparison. All composite-adjunction associators
   are present in the two pasting definitions.
5. Checked each of a_R,t_S,a_S,b_R against the node's prescribed transposes,
   checked χ's conjugation orientation (right-adjoint square inverted), and
   checked that the displayed main equality has source L_E,S(T_E M) and
   target Res_b(T₀' L_D,R' M').
6. Checked all chain generator formulas against the source's opposite tensor
   order, and the representative equation against the bar augmentation
   normalization so that multiplication by an unspecified scalar is excluded.

The item node's statement, stmt_deps, proof and proof_deps remain unchanged.
