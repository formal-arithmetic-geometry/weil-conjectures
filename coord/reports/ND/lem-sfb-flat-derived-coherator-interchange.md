## Worker report

This delivery states `lem-sfb-flat-derived-coherator-interchange` in
`Sheaf.AlgebraicGeometry.FlatDerivedCoheratorInterchange`. The main theorem is
`AlgebraicGeometry.Scheme.Modules.exists_flatDerivedCoheratorInterchange`; the
second theorem is its affine-open clause. Both proofs are `sorry`, and both
carry this same DAG node and the appropriate steps of its complete proof plan.
No mathematical assertion is proved in this stage-2 delivery. Every definition
has actual data, and there are no new independent notions or dependency repairs.
The node copy changes only `lean`.

The source was read locally at `literature/stacks-project/perfect.tex`,
`lemma-flat-pushforward-coherator` (Tag 08D8), including the four Hom
identifications, and its application in `lemma-argument-proves` (Tag 09T6).
The existing upstream `DQCoheratorAdjunction` concerns the full subcategory
D_QCoh of the module derived category, on qcqs schemes. It is not the present
D(QCoh) coherator on arbitrary schemes and does not state this comparison.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

1. Schemes and the given map are `{Z Y : Scheme.{u}} (f : Z ⟶ Y)`.
   `[Flat f] [QuasiCompact f] [QuasiSeparated f]` are exactly flatness and
   relative quasi-compactness/quasi-separatedness. Mathlib's quasi-compactness
   means inverse images of quasi-compact opens are quasi-compact; its affine
   test characterization gives precisely the node's affine-open formulation.
   There is no hypothesis that either Z or Y is qcqs, affine, separated,
   Noetherian, nonempty, or of any characteristic.
2. A_T is literally `(SheafOfModules.isQuasicoherent T.ringCatSheaf).FullSubcategory`
   and i_T is its existing `.ι`. The supplied `dZ`, `dY` are the existing
   `DerivedCoheratorAdjunctionData` of the recorded dependency. They contain
   the induced abelian structures, total derived coherators, derived adjunctions,
   normalization and canonical shifts. `flatDerivedCoheratorInterchangeType`
   installs precisely their instances, never an unrelated abelian structure.
   Their actual `derivedAdjunction.unit` and `.counit` are used in every identity.
3. The module categories are `SheafOfModules.{u} T.ringCatSheaf`, identical to
   the recorded `moduleRings T.toRingedSpace` encoding. The independent
   `[HasDerivedCategory.{wZ} ...]` and `.{wY}` parameters select arbitrary
   localization universes, as in the coherator dependency. The quasi-coherent
   derived categories use that dependency's always available localization.
   All complexes are `CochainComplex ... ℤ`; every derived category is unbounded.
4. `flatCoheratorPullback` and `flatCoheratorPushforward` are the standard
   `ObjectProperty.lift` of i_Y followed by the actual `tensorPullback f`, and
   i_Z followed by actual `pushforward f`, respectively. Their object and map
   data are those functors, not arbitrary substitutes. The dependent sum in
   `flatDerivedCoheratorInterchangeType` asserts preservation of quasi-coherence
   for both functors as part of the conclusion. It does not assume it as a
   hypothesis or select proof-postponed objects.
5. The package `FlatDerivedCoheratorInterchangeData` states module tensor
   pullback's additivity, preservation of finite limits and finite colimits,
   and the same exactness for its quasi-coherent restriction P₀. It also states
   additivity of actual F=f_*|QCoh, the existence of K-injective resolutions,
   and the underived adjunction. `ordinaryNormalization` says its transpose is
   precisely the transpose under `tensorPullbackSectionAdjunction f`, with the
   two ordinary inclusion squares. Hence it cannot be an unrelated adjunction.
6. P_f is exactly `P₀.mapDerivedCategory`. Phi_f is exactly the recorded
   `F.rightDerivedFunctorOfQuasiIsoResolutions resolutions`, with its recorded
   comparison unit. Its existence is inherited from the recorded definition's
   total-derived universal property, supplied with resolutions by the package.
   The package's `adjunction` and `derivedNormalization` supply the induced
   adjunction and its localized underived Hom formula. Its unit is u_f.
7. R_f is exactly `schemeDerivedDirectImage f`; it is never an arbitrary
   direct-image functor. The package's `moduleAdjunction` has left functor
   `(tensorPullback f).mapDerivedCategory`, using the exactness just concluded.
   `moduleNormalization` specifies the induced Hom bijection using the actual
   `RingedSpace.moduleDirectImage ... .rightDerivedFunctorUnit` computed by
   K-injectives. Its unit is v_f.
8. `pullbackInclusion` is the typed version of I_Z P_f = f^* I_Y. Its
   `pullbackInclusionNormalization` fixes its value as the standard derived
   composition comparisons and derived image of the ordinary identity square.
   `flatCoheratorRightAdjointComparison` is actual `Adjunction.rightAdjointUniq`
   for `(eY.comp moduleAdjunction).ofNatIsoLeft pullbackInclusion.symm` and
   `adjunction.comp eZ`. Thus lambda is specifically the isomorphism obtained
   from the source's four Hom identifications, not an arbitrary isomorphism.
   In Lean's functor-composition order its type is `R ⋙ CY ≅ CZ ⋙ Phi`.
9. The exact left functors and derived inclusions carry Mathlib's canonical
   triangulated/shift structures. For Phi, fields `shift`, `canonicalShift`,
   `triangulated`, and `compatible` supply the canonical structure (the
   comparison unit commutes with shifts) and actual adjunction compatibility.
   R uses the existing canonical right-derived shift structure, installed
   explicitly in the specializing definition; `moduleCompatible` applies to
   that same structure. `comparisonShift` asserts compatibility of the actual
   lambda. The supplied coherator data already normalize their e_T and d_T.
10. The `identities` field quantifies over EVERY natural isomorphism
    `c : Phi ⋙ IY ≅ IZ ⋙ R`. Its hypothesis is the node's localized derived-unit
    equation on every complex B. `flatCoheratorLocalizedUnit` writes the
    homotopy-to-complex transport explicitly, through `quotientCompQhIso`,
    `mapHomotopyCategoryFactors` and the actual unit. The left side is the
    localized F unit mapped by IY and followed by c. The right side is the
    ordinary pushforward/inclusion square followed by the module-derived unit
    at i_Z B and R of the inverse inclusion factorization. No preservation of
    K-injectives by i_Z is required, no arbitrary comparison replaces this one,
    and none of the three desired identities is assumed as a hypothesis.
11. `FlatCoheratorInterchangeIdentities` first conjunct is
    `eY.unit.app (Phi.obj B) ≫ CY.map (c.hom.app B) ≫ lambda.hom.app (IZ.obj B)
      = Phi.map (eZ.unit.app B)`.
    This is exactly lambda C_Y(c_B) e_Y(Phi B) = Phi(e_Z(B)), with Lean's
    left-to-right `≫` convention.
12. Its second conjunct is
    `eY.counit.app (R.obj E) = IY.map (lambda.hom.app E) ≫
      c.hom.app (CZ.obj E) ≫ R.map (eZ.counit.app E)`.
    This is exactly d_Y(RE) = R(d_Z(E)) c_(C_ZE) I_Y(lambda_E).
13. Its third conjunct is
    `IY.map (adjunction.unit.app H) ≫ c.hom.app (P.obj H) =
      moduleAdjunction.unit.app (IY.obj H) ≫ R.map (pullbackInclusion.inv.app H)`.
    This is the node's c_(PH) IY(u(H)) = v(IY H), with the necessary canonical
    identification I_Z P = K I_Y written explicitly on the right-hand side.
    The inverse orientation is forced by its target, R(I_Z(PH)).
14. `exists_flatDerivedCoheratorInterchange_affineOpen` takes `[CompactSpace Y]`
    and `[QuasiSeparatedSpace Y]`, any `U : Y.Opens`, and
    `(hU : IsAffineOpen U)`. It concludes exactly the same package for U.ι,
    with the supplied dU and dY. Flatness and relative qcqs of U.ι are
    conclusions to be justified in its proof, not extra assumptions.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, with
  `Flat.iff_flat_stalkMap` identifying the node's stalkwise definition.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`:
  `AlgebraicGeometry.QuasiSeparated`; its field is quasi-compactness of the diagonal.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, via the scheme imports.
- `Sheaf.AlgebraicGeometry.SchemeDerivedCoheratorAdjunction`:
  `AlgebraicGeometry.Scheme.Modules.DerivedCoheratorAdjunctionData` and
  `exists_schemeDerivedCoheratorAdjunction`. Read its full structure and theorem.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction` and the
  publicly imported actual `tensorPullback` functor. The adjunction is fixed
  uniquely by its ordinary section unit 1 tensor m, not a free Nonempty choice.
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `AlgebraicGeometry.schemeDerivedDirectImage`; its source and the full
  `RingedSpaceDerivedDirectImage` construction were read.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions` and its unit,
  publicly exposed by the coherator dependency; full signatures/docstrings read.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  the open-specialization uses the actual scheme open inclusion U.ι.
- Exact functor definitions and composition comparisons use
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` and
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
  `Mathlib.CategoryTheory.Adjunction.Unique` provides `Adjunction.rightAdjointUniq`.
- Recorded proof-dependency modules are imported with plain `import`, except
  `RightDerivedFunctor.Triangulated`, which is also a public statement dependency
  because its concrete canonical shift instance is used in the specializing definition.
  The three Mathlib leaves for exact factorization, composite adjunction and
  unique right adjoint are exposed by the exact-functor/adjunction imports;
  the affine qcqs Mathlib leaf is exposed through the scheme/qs imports.

Edge cases checked before writing:

- Identity morphisms: no special exclusion; the actual derived functors and
  normalization still apply. An arbitrary scalar rescaling of c is not silently
  accepted: its compatibility with the fixed derived comparison unit is required.
- Empty schemes and the empty affine open: no `Nonempty` assumption on a scheme
  or an open, and no nonzero-ring assumption. `Nonempty` in the theorem means
  existence of the construction package, not of points.
- Y non-separated or non-quasi-compact: the main theorem assumes only relative
  qcqs of f; the separate affine-open clause has the node's qcqs base assumptions.
- Unbounded complexes: no boundedness, finite amplitude, cohomological dimension,
  injective preservation by the inclusion, or Noetherian condition was inserted.
- Independent localization universes: wZ and wY are separate, while the
  quasi-coherent localizations are exactly those fixed by dZ and dY. No unwanted
  equality of universes was imposed.
- The first two identity targets were checked with the domains of the actual
  units/counits; the third includes the necessary inverse pullback/inclusion
  comparison. Lambda's direction matches C_Y R to Phi C_Z.

Searches (2026-10-24):

- `msearch.py ... leanfinder "Flat quasi compact quasi separated pushforward
  commutes with derived coherator with normalized adjunction unit and counit"`:
  8 hits, ordinary sheaf pushforward adjunction and continuous-sheafification
  compatibility; no unbounded scheme coherator comparison.
- `msearch.py ... loogle "CategoryTheory.Adjunction.rightAdjointUniq,
  CategoryTheory.Functor.IsRightDerivedFunctor"`: 0 hits. These separate abstract
  ingredients do not already state the item.
- `msearch.py ... grep "coherator|rightAdjointUniq"`: 19 hits, principally
  `Mathlib/CategoryTheory/Adjunction/Unique.lean`; reused right-adjoint uniqueness.
- `msearch.py ... leansearch "Right derived direct image for flat qcqs scheme
  morphism and quasi coherator with normalized unit counit identities"`: 8 hits,
  right-derived universal constructions, derived epsilon and ordinary scheme
  pushforward adjointness; no exact statement.
- `rg -n "coherator|Coherator"` in both `lean/WeilConjectures` and `lean/Sheaf`
  found the scheme coherator dependency, its affine comparison and the distinct
  upstream D_QCoh coherator. Read the former and the upstream DQCoheratorAdjunction
  signature; neither contains this flat interchange theorem.
- `rg -n "lem-sfb-flat-derived-coherator-interchange"` in both library roots:
  no existing declaration. Also searched all roots including Mathlib for the
  proposed helper/package names before adding them: no name collision.
  A follow-up search for QCoh pullback/pushforward definitions found
  `flatSectionQCohPushforward` (closed-immersion derived D_QCoh) and
  `spaceQCohPullback` (algebraic spaces and derived D_QCoh); their signatures
  were read and differ from the ordinary QCoh functors required here.
- Read the actual tensor pullback, normalized adjunction, ordinary QCoh
  pushforward theorem, QCoh Grothendieck structure, exact derived factorization,
  derived-adjoint square comparison and normalized exact-square derived unit.

Compiler-guided adjustments concern only elaboration: mark the actual functor
lifts noncomputable, use a generic inclusion-square package to avoid competing
full-subcategory zero/addition instances, and explicitly install the recorded
coherator/additive and module K-injective/shift structures in its specialization.
These do not change the mathematical statement or any dependency record.

No STATEMENT-DISPUTED finding, statement correction, or source fault.

## Validation

Final `scompile.py` passed both the module-mode sandbox check (42.0 s) and
the named library-module check (48.5 s), each within its 60 s limit, with no
errors or unexpected warnings. The exact final source has two postponed proofs.
Delivery preflight follows. No global build, local compilation, direct Git command, or live
repository write is used.

## Second reading by ND

Independent clause-by-clause reading (maintainer reviewer, 2026-10-24), against the
node, Stacks perfect.tex Tag 08D8 (lemma-flat-pushforward-coherator, four Hom
identifications) and its use in Tag 09T6, and the recorded dependency declarations.
The earlier section text said only that no second worker reading took place.

Node list and the Lean that renders it:

1. f : Z → Y flat, quasi-compact, quasi-separated: `(f : Z ⟶ Y) [Flat f]
   [QuasiCompact f] [QuasiSeparated f]` (Mathlib, recorded by the three def stmt_deps).
   Nothing stronger is assumed. Correct.
2. A_T = QCoh(O_T) and I_T ⊣ C_T with e_T, d_T: `(SheafOfModules.isQuasicoherent
   T.ringCatSheaf).ι` with arbitrary `DerivedCoheratorAdjunctionData` dZ, dY (recorded
   lean of lem-sfb-scheme-derived-coherator-adjunction). Their abelian structure,
   derived category and shift instances are installed in
   `flatDerivedCoheratorInterchangeType`, and `dT.derivedAdjunction.unit/.counit` are
   used. Correct: the identities hold for every such datum.
3. Unbounded categories: `CochainComplex _ ℤ`, `DerivedCategory`. Ambient
   localization universes wZ and wY are independent. Correct.
4. P_f = termwise tensor pullback: `(flatCoheratorPullback f hP).mapDerivedCategory`.
   This is the lift of the recorded `tensorPullback f` (def-pc-module-pullback). The
   preservation of quasi-coherence, hP, is a Σ' conclusion. Correct.
5. R_f = `schemeDerivedDirectImage f` (def-pc-derived-direct-image, abbrev for
   `(moduleDirectImage _).rightDerivedFunctor`), with its own unit as ηG. Correct.
6. Φ_f = total right derived functor of f_*|QCoh:
   `F.rightDerivedFunctorOfQuasiIsoResolutions resolutions` (def-sfb-right-derived-functor).
   F is the lift of `pushforward f`, and hF is a conclusion. The resolutions are a
   Prop field, so Φ does not depend on the choice. Correct.
7. P_f ⊣ Φ_f with unit u_f: field `adjunction`. `derivedNormalization` pins its
   homEquiv on all Qh-objects, hence its unit (Qh is essentially surjective). The
   restricted ordinary adjunction is pinned via `ordinaryNormalization` against
   `tensorPullbackSectionAdjunction f` (recorded, uniquely normalized). Correct.
8. Exact module pullback with derived adjoint R_f and unit v_f: fields
   `moduleAdjunction`/`moduleNormalization`. These are pinned the same way by the
   K-injective unit ηG. Correct.
9. λ : C_Y R_f ≅ Φ_f C_Z from uniqueness of right adjoints to I_Z P = f^* I_Y:
   `flatCoheratorRightAdjointComparison` = `rightAdjointUniq` of
   `(eY.comp b).ofNatIsoLeft s.symm` and `a.comp eZ`. Here s = `pullbackInclusion`,
   which is pinned to the derived image of the ordinary identity square. Its type
   is `R ⋙ CY ≅ CZ ⋙ Φ` (Lean order). This is canonical, not chosen. Correct.
10. Canonical triangulated/shift structures: Mathlib's for exact functors, and
    `dT.shift` for C_T. For Φ, the `shift` field is pinned by `canonicalShift`
    (unit CommShift, iso on K-injectives), with `triangulated`. For R it is the
    upstream instance `Functor.instCommShiftDerivedCategoryRightDerivedFunctorInt`
    (canonical, transported through K(Inj) ≌ D). Its unit is CommShift by the
    upstream `canonical_unit_commShift` lemmas. `compatible`, `moduleCompatible` and
    `comparisonShift` hold for these structures. Correct.
11. Hypothesis on c: the `identities` field quantifies over every
    `c : Φ ⋙ IY ≅ IZ ⋙ R`. Its premise is, on every complex B, (IY of the localized
    F-unit) followed by c equals the ordinary square followed by the module
    K-injective unit at i_Z B. I checked every arrow type. This premise determines c
    on Q(J) for K-injective J, hence everywhere. It is the characterization of
    lem-sfb-exact-square-right-derived-unit and is not stronger than the node.
    Correct.
12. Identity 1 `eY.unit.app (Φ B) ≫ CY.map (c.hom.app B) ≫ λ.hom.app (IZ B) =
    Φ.map (eZ.unit.app B)`: λ_{I_ZB} C_Y(c_B) e_Y(ΦB) = Φ(e_Z B). Types checked. Correct.
13. Identity 2 `eY.counit.app (R E) = IY.map (λ.hom.app E) ≫ c.hom.app (CZ E) ≫
    R.map (eZ.counit.app E)`: d_Y(RE) = R(d_Z E) c_{C_ZE} I_Y(λ_E). Correct.
14. Identity 3 `IY.map (a.unit.app H) ≫ c.hom.app (P H) = b.unit.app (IY H) ≫
    R.map (s.inv.app H)`: c_{PH} I_Y(u H) = v(I_Y H). The identification I_ZP = KI_Y
    is made explicit by s.inv. Correct.
15. Affine-open clause: `[CompactSpace Y] [QuasiSeparatedSpace Y] (U) (hU :
    IsAffineOpen U)`, with the same package for `U.ι`. Flatness/qcqs of U.ι are left
    to the proof. Correct.

Edge cases: f = 𝟙 and the empty scheme / empty affine open are covered (no
Nonempty or nonzero-ring hypothesis). Non-quasi-compact or non-separated Y is
allowed in the main theorem. There is no boundedness, Noetherian or
K-injective-preservation hypothesis. Universes: Scheme.{u}; module localization
universes wZ, wY are free; the QCoh localizations are the ones fixed in dZ, dY.

One definition per notion: there is no existing flat-interchange declaration
(rg coherator in lean/Sheaf and lean/WeilConjectures; no collision for the new
names). The upstream DQCoheratorAdjunction is the D_QCoh coherator, a different
notion. The helpers are real data (functor lifts, a localized unit composite,
rightAdjointUniq, and a Prop predicate). None of them is hollow.

Records: node fields other than `lean` and all nine stmt_dep files are
byte-identical to live. `lean.statement` is verbatim in the file. The nine
`lean.declarations` match the file.

Advisory: the canonical CommShift instance on R_f is owned by
lem-pc-right-derived-functor-triangulated, which is a proof_dep and not a stmt_dep.
It is the canonical structure the node names, so this is an advisory only.
Nothing was changed in the Lean or the records. This section replaces the earlier
direct-delivery note.
