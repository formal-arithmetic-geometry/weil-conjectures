## Worker report

The module `Sheaf.AlgebraicGeometry.AffineDerivedCoherator` states
`AlgebraicGeometry.Scheme.Modules.affineDerivedCoherator_comparisons`, with a
single postponed proof. It asserts invertibility of the specified derived
coherator unit everywhere and of its counit on quasi-coherent derived objects.
The node is unchanged except for its `lean` field. There are no new nodes,
dependency repairs, statement corrections or disputed statements.

Hypothesis and clause correspondence:

- “T an affine scheme”: `(X : Scheme.{u}) [IsAffine X]`. Mathlib's `IsAffine`
  means that the canonical map to Spec of global sections is invertible, the
  usual affine condition, and includes the empty scheme.
- The module-sheaf category is `SheafOfModules.{u} X.ringCatSheaf`, with its
  existing Mathlib category and abelian structures. `X.ringCatSheaf` is the
  same ring sheaf as `moduleRings X.toRingedSpace` used by the recorded
  scheme-derived-category definitions; compilation checks this compatibility.
- A_T is exactly `(SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory`.
  This reuses the existing full category, with no alternative QCoh definition.
- The unbounded localization of the ambient module category is supplied by
  `[HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]`. Its morphism
  universe is arbitrary `w`; this is the dependency's localization infrastructure,
  not an added geometric assumption. The QCoh abelian and derived-category
  structures are the fields `d.abelian` and `d.derivedCategory` of the recorded
  adjunction package, explicitly passed to `DerivedCategory` in the B binder.
- I_T, C_T and their specified adjunction are supplied together by
  `(d : DerivedCoheratorAdjunctionData
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι)`. Its left adjoint is exactly
  the termwise derived inclusion; its right adjoint is the recorded total right
  derived functor of its ordinary coherator. The package includes normalization
  by termwise underived adjuncts on K-injective representatives. The dependency
  `exists_schemeDerivedCoheratorAdjunction` supplies such data for every scheme.
  Quantifying over this data preserves the statement about the given adjunction,
  without selecting a different equivalence or making a data definition by choice.
- “For every B in D(A_T), e_T(B) is an isomorphism” is the first conjunct,
  `∀ B : @DerivedCategory ... d.abelian d.derivedCategory,
  IsIso (d.derivedAdjunction.unit.app B)`.
- “For every E in D_QCoh(O_T), d_T(E) is an isomorphism” is the second conjunct,
  `∀ E : schemeDerivedCategory X, schemeDerivedQCohProperty X E →
  IsIso (d.derivedAdjunction.counit.app E)`. The recorded predicate means
  quasi-coherence of every integer-degree homology sheaf. Quantifying over the
  ambient object with this predicate is exactly quantifying over that full
  subcategory; the counit is the ambient adjunction's counit.
- No boundedness, finite-type, characteristic or Noetherian assumptions occur.
  Both clauses concern actual morphisms via `IsIso`, not merely isomorphism of
  their endpoints or cohomology objects.

Statement dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms;
  affineness is `AlgebraicGeometry.IsAffine` from
  `Mathlib.AlgebraicGeometry.AffineScheme`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`, publicly exposed by the
  coherator-adjunction import: the underlying Mathlib
  `SheafOfModules.IsQuasicoherent` / `isQuasicoherent` predicate (the finite-type
  conjunction is not substituted for quasi-coherence).
- `Sheaf.CategoryTheory.RingedSiteModules`, publicly exposed by that same import:
  `CategoryTheory.ringedSiteModules` abbreviates the reused `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, exposed by that same import:
  `DerivedCategory`, `HasDerivedCategory`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `schemeDerivedCategory`, `schemeDerivedQCohProperty`.
- `Sheaf.AlgebraicGeometry.SchemeDerivedCoheratorAdjunction`:
  `AlgebraicGeometry.Scheme.Modules.DerivedCoheratorAdjunctionData` and
  `exists_schemeDerivedCoheratorAdjunction`; all package fields, their full types
  and their normalization were read.

Proof dependencies have plain imports, in accordance with the stage-2 rule:
`Mathlib.AlgebraicGeometry.Modules.Tilde` (`tilde.adjunction`, its invertible unit,
`Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent`);
`Sheaf.AlgebraicGeometry.QuasiCoherentGrothendieckGenerators`
(`quasiCoherent_grothendieck_generators`);
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
(`Functor.mapDerivedCategoryFactors`);
`Mathlib.CategoryTheory.Localization.Predicate` (`Localization.lift`,
`fac`, `liftNatTrans`, `liftNatIso`, `natTrans_ext`);
`WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence`
(`exists_affineQCohDerivedEquivalence`);
`Mathlib.CategoryTheory.Adjunction.FullyFaithful`
(`Adjunction.unit_isIso_of_L_fully_faithful`). The statement dependency for the
specified coherator adjunction is already public. No proof import is omitted.

Source and edge cases: read `literature/stacks-project/perfect.tex`,
`lemma-affine-coherator` (Tag 08D9), especially (3) and its reduction to the
unbounded affine comparison. The empty affine scheme (Spec of the zero ring)
remains permitted; both module categories are then zero categories and both
claims are valid. The zero complex is allowed in both clauses. Complexes may
be unbounded in either direction and cohomology is tested for every integer,
including degree zero. Arbitrary non-Noetherian affine coordinate rings and
all characteristics remain permitted. The restriction to quasi-coherent E is
essential: no assertion about the counit on arbitrary non-quasi-coherent
objects is made. The two localization universes are those of the existing
package, and no equality of universe parameters is introduced.

Searches actually run on 2026-10-24:

- `msearch.py ... leansearch`: “Affine scheme derived coherator adjunction
  unit and counit are isomorphisms”. Eight hits: Gamma-Spec adjunction
  comparisons, abstract conversion of an adjunction to equivalence maps,
  the abstract derived counit formula, and the fully faithful unit criterion.
  None states the affine derived coherator result.
- `msearch.py ... leanfinder`: “On an affine scheme the unbounded derived
  coherator adjunction has invertible unit and counit on objects with quasi
  coherent cohomology”. Eight hits: abstract derived-adjunction constructions
  and their unit/counit formulas, `DerivedCategory.quotientCompQhIso`, exact
  derived factorization, and K-injective Hom calculation. None is this affine
  QCoh comparison theorem.
- `msearch.py ... loogle`: `CategoryTheory.Adjunction.unit_isIso_of_L_fully_faithful`.
  Two hits: the exact abstract unit criterion and an adjunction-triple identity.
  The criterion is already a proof dependency, not the geometric statement.
- `msearch.py ... grep`: `coherator|[Aa]ffine.*[Dd]erived|[Dd]erived.*[Aa]ffine`.
  Zero Mathlib hits.
- `rg -n` on both `lean/WeilConjectures` and `lean/Sheaf` for the same pattern,
  followed by the narrower `coherator|Coherator` search and reading the relevant
  sources: the normalized scheme coherator package is the statement dependency;
  the affine derived equivalence is the proof dependency. The upstream
  `DQCoheratorAdjunction` concerns inclusion of D_QCoh into D(O) on qcqs schemes,
  rather than D(QCoh), and is not this theorem. Stack and algebraic-space
  coherators concern different categories. Other affine-derived hits concern
  tensor/pushforward or etale geometry.
- `grep -rn "lem-sfb-affine-derived-coherator" lean/WeilConjectures`: no match.
- `rg -n "affineDerivedCoherator_comparisons" lean/Sheaf lean/WeilConjectures
  dag/lean_names_upstream.json`: no collision.

Validation: every delivered Lean file is compiled separately by `scompile.py`;
only the expected sorry warning is allowed. The dry run and delivery outputs
are the final mechanical validation.

## Second reading by Q138

Final worker rereading, not an independent agent review: I compared the complete
node statement and the written signature again. The affine binder supplies the
sole geometric hypothesis; the data argument is the exact recorded normalized
adjunction; B uses that package's own derived QCoh category and E uses the shared
ambient category and shared quasi-coherence predicate. The conjunction matches
the two universal assertions, with the unit and counit in their correct
categories and orientations. There is no replacement of these maps by arbitrary
isomorphisms. The full five-step proof is in the theorem docstring and all
recorded proof dependencies have imports. No mismatch was found and no statement
change was made. The maintainer's independent review remains the review specified
in the dispatch brief; no other agent was started.
