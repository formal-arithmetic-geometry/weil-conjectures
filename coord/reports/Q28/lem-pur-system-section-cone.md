## Worker report

The module `Sheaf.Paper.PuritySystemSectionCone` states
`CategoryTheory.PuritySectionCone.coneCalculation`. Its only postponed proof is this
theorem. Its docstring contains all six steps of the node's proof, including the
compatible Hom-complex lifting square and the explicit filler. All helper data and
maps have real definitions; `ConeCalculation` packages the conclusions of the one
theorem, rather than defining a cone by choosing an unproved existence witness.

The statement of the DAG node is unchanged. There are no new nodes, dependency
repairs, or disputed statements. The helper structures package the hypotheses and
conclusions of this item; they do not create a second section category or a second
mapping-cone construction.

Hypotheses, clause by clause:

* The small site is `{C : Type u} [Category.{v} C] {J : Precoverage C}` with
  `_hJ : J.IsSiteForCoverings`, using exactly the recorded site predicate.
  The topology of every coefficient sheaf is `J.toGrothendieck`.
* The inverse sequence is `B : I ⥤ Sheaf J.toGrothendieck CommRingCat`, where
  `_index : I ≌ ℕᵒᵈ` specifies precisely the inverse natural-number sequence.
  Index zero corresponds to the node's coefficient `B_1`. The equivalent indexing
  category permits the Hom universe required by the published Quillen-diagram
  interface without identifying the site's object and morphism universes.
  Coefficient and module universes are `max u v w`, containing the small site;
  the freely chosen `w` permits arbitrary larger coefficient universes.
* The component category is the dependency's `CoefficientFlatModel.Complex`,
  transparently `CochainComplex (CoefficientFlatModel.Modules (B.obj i)) ℤ`.
  `flat i : CoefficientFlatModel.FlatModelData (B.obj i)` supplies exactly the
  flat model, and `_flat_models` identifies each chosen fiber model with it.
* `A : CoefficientDiagram B` contains the published `QuillenSections.Diagram`.
  Consequently each transition is an enriched Quillen adjunction with all
  pseudofunctor coherence equations. Its `restriction_eq` identifies the right
  adjoint with the termwise lift of Mathlib's actual `SheafOfModules.restrictScalars`
  along `B.map α`. Its left adjoint is therefore ordinary tensor scalar extension,
  uniquely up to the canonical adjunction-preserving isomorphism. No arbitrary
  extension map, noncanonical choice, or flatness of a coefficient homomorphism is
  assumed. `adjointArrow` takes precisely this adjunction mate.
* `CoefficientDiagram.composition` says that the mate of the composite tensor
  comparison is the identity on the underlying semilinear sections, in every
  degree, object and element. `unit` gives the same normalization for identity
  arrows. These characterize the ordinary tensor associators and units by the
  adjunction; the comparison maps are not arbitrary coherent isomorphisms.
* `QuillenSections.Section A.diagram` is the recorded category of strict sections,
  with its original transition, unit, composition, and compatible-map equations.
  The section `ModelCategory`, its `DgModel`, its enrichment, `π`, and `_end`
  give the dg section model and canonical end over the chosen fiber enrichments.
  `_weak` is exactly the componentwise quasi-isomorphism criterion, and `_fib`
  is exactly the componentwise fibration criterion. The selected fiber flat models
  themselves give the canonical quasi-isomorphism weak-equivalence criterion.
* `Q` is an arbitrary strict section, and `_cofibrant : IsCofibrant Q` is its
  stated cofibrancy assumption. Cofibrancy of the cone inclusion is a conclusion.

Conclusions, clause by clause, are the fields of `ConeCalculation A Q`:

* `coneSection`, `shiftSection`, `coneIso`, and `shiftIso` specify the actual
  componentwise identity cone and positive shift using Mathlib's constructions.
  Mathlib's cone already has the node's summand order `Q^(k+1) ⊞ Q^k` and
  differential `(-dx, x+dy)`, and its shift has differential `-d`.
* `transition_first` and `transition_second` specify both projections of the
  semilinear cone transition. They force exactly `(x,y) ↦ (s x,s y)` under the
  scalar-extension/restriction adjunction. In particular they prohibit extra
  off-diagonal transition terms.
* `inclusion` is a morphism in the actual section category. `inclusion_formula`
  identifies it on every component with `mappingCone.inr`, namely `y ↦ (0,y)`.
  `cofibration` asserts it is a cofibration in the given section model.
* `projection` is a section map to the componentwise shift. Its formula is the
  negative of Mathlib's triangle third map: Mathlib's triangle uses `-p`, so this
  is exactly the node's positive projection `(x,y) ↦ x`.
  `annihilates` and `cokernel` are the cokernel universal property, quantified over
  every section and every section map vanishing on the inclusion, with a unique
  factorization. Componentwise zero is used only to write zero morphisms without
  introducing a new instance on the section category. Since section maps are
  compatible families, componentwise vanishing is precisely vanishing there.
  The projection formula and diagonal cone transitions also fix the shifted
  transitions, rather than permitting a different system with shifted components.
* `contraction` is a genuine `Homotopy (𝟙 _) 0` on each component; hence its
  differential identity is `dH+Hd=1`. `contraction_compatible` says that this whole
  family commutes with every semilinear transition in every pair of degrees.
* `zeroSection`, `zero_isZero`, and `zero_components` specify the zero section
  categorically and on all evaluations. `toZero` is its unique incoming map.
  `component_quasiIso` asserts the componentwise quasi-isomorphism, and
  `weakEquivalence` asserts its weak equivalence in the given section model.
  The existence formulation is an invariant presentation of these canonical
  objects and maps: the component isomorphisms and all displayed normalizations
  fix them, rather than replacing any canonical map by an arbitrary witness.

Recorded dependency declarations read and used:

* `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`, publicly imported through the
  recorded flat-model module.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  used by the recorded `CoefficientFlatModel.Modules` abbreviation.
* `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`.
* `Sheaf.Paper.SheafFlatModel`: `CategoryTheory.CoefficientFlatModel.Modules`,
  `Complex`, `FlatModelData`, and `exists_flatDifferentialGradedModel`.
  The theorem binds the exact model data whose existence the recorded theorem
  asserts, rather than introducing a second flat model.
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars` and its additive instance.
* The recorded dependency `lem-coef-quillen-section-rectification` supplies the
  interfaces `CategoryTheory.QuillenSections.Diagram`, `DgModel`, `Section`, and
  `IsSectionEnd` through `Sheaf.CategoryTheory.DgQuillenDiagram` and
  `Sheaf.CategoryTheory.StrictQuillenSections`. The broad
  `Sheaf.CategoryTheory.QuillenSectionRectification` wrapper was not imported in
  the repaired packet: compiling it currently traverses an unrelated
  `SpaceValuedStraightening` definition that lacks a `noncomputable` declaration.
  The cone statement uses only these foundational interfaces and does not assume
  `quillenSectionRectification`, `Rectification`, or any conclusion of this node.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: the recorded abstract-derived
  category module, providing the stated cochain/shift conventions. The actual
  cone API is `Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated`, read
  together with `MappingCone` and `HomotopyCofiber`.

The proof dependency `lem-coef-projective-cochain-monoidal-model` currently has
neither a recorded Lean module nor a Mathlib match, so there is no module to import
for it. Its role and precise generator remain in the proof docstring. It is not a
missing notion needed to type this statement, and no proof is being delivered.

Edge cases checked before writing: the zero section gives a zero cone and shift;
for a complex concentrated in degree zero the cone has adjacent degrees -1 and 0
with identity differential and contraction in the reverse direction. For zero
differentials in Q, the cone differential still has the identity off-diagonal
entry, so the cone is not incorrectly treated as a zero-differential direct sum.
The summand order and the negative sign in Mathlib's triangle were checked in
the source and against Stacks `derived.tex`, definition-cone (Tag 014E).
Identity arrows and all composites are included in the coherence hypotheses and
transition/contraction clauses. Nothing requires coefficient homomorphisms to be
flat or surjective, and zero coefficient rings and empty sites are allowed.
All degrees range over ℤ, and no boundedness is imposed.

Searches for an existing declaration (logged by the prescribed `msearch.py` with
the sandbox set to this delivery):

* LeanFinder: “A cofibrant strict semilinear section includes into the contractible
  cone of its identity by a cofibration with shifted cokernel”. Returned generic
  mapping-cone and homotopy-cofiber facts, including
  `CochainComplex.mappingCone.homotopyToZeroOfId`; no section-model theorem.
* Loogle: `CochainComplex.mappingCone.homotopyToZeroOfId`. One exact generic
  contractibility theorem, without section compatibility or a cofibration clause.
* Mathlib grep: `homotopyToZeroOfId|mappingCone.*[Cc]ofib|[Cc]ofib.*mappingCone`.
  Five hits in MappingCone/Pretriangulated, no theorem for semilinear sections.
* LeanSearch: “The cone of the identity on a cofibrant strict section is
  contractible and the inclusion is a cofibration with shifted cokernel”. Generic
  cylinder cofibration and mapping-cone results only.
* Direct `rg` on the source `WeilConjectures` tree for the node id, and on that
  tree and the shared `lean/Sheaf` for `PuritySectionCone|coneCalculation|ConeCalculation`,
  found no existing declaration. Read the published Quillen-section and flat-model
  modules rather than reimplementing their notions.

Compilation and the required delivery dry run are performed through `scompile.py`
and `deliver2.py`; no live source edits, direct Git commands, or global builds.

## Second reading by Q28

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
