## Worker report

The module `Sheaf.AlgebraicGeometry.CondensedTateTwists` defines the condensed Tate
module and every integral twist as real data. Its primary declaration is
`AlgebraicGeometry.ProEtale.tateTwistDerived`; the node lists all eleven declarations,
including the coefficient inclusion and its ring-hom instance. There are no new
sorry terms, theorem declarations, independent nodes, dependency modules, or statement
corrections. All original node fields other than `lean` are retained.

Source read: the complete verbatim archived `TateTwist/ProEtale.lean` exhibit in the
maintenance evidence, particularly lines 79–179, with the blob recorded in the node.
Also read the published coefficient, scalar-extension, module-tensor and free-module
sources, and the full recorded roots-of-unity declaration and transition definitions.
The archived module is unavailable in the published library (`scompile.py --source
WeilConjectures.TateTwist.ProEtale` reports source unavailable), so it cannot be imported
or recorded as existing. The construction is supplied here, using its available
canonical ingredients and names. The already recorded internal-module equivalence
was read with `scompile.py --source Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`;
it is published even though absent from the older local side checkout.

Hypothesis and clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Universe and small-site convention | Explicit `universe u`; `X : Scheme.{u}`, its existing `X.ProEt` and `ProEt.topology X`; abelian sheaf values in `AddCommGrpCat.{u + 1}`. This retains site object universe `u+1` and morphism universe `u`. |
| A prime ell and an arbitrary scheme X | `(ℓ : ℕ) [Fact ℓ.Prime]` and `(X : Scheme.{u})`. No other scheme, field, characteristic or invertibility binders. |
| Z_ell inside Q_ell | Existing `PadicInt`, `Padic`, and `padicIntCondensedRingToPadicCondensedRing`. |
| Continuous integral condensed coefficients | `Profinite.continuousMapRingObj ℤ_[ℓ]`, the abelian sheaf underlying `padicIntCondensedRing`; sections are the existing universe-lifted continuous functions with pointwise operations. |
| Finite-extension-valued algebraic-closure coefficients | Exactly `Profinite.padicAlgClRingObj ℓ` from the two-colimit dependency's coefficient construction; no continuous-function sheaf on the whole topological algebraic closure is substituted. |
| Geometric pullback, R_X, B_X | The existing `condensedRingObj` applied to these two ring objects; this is `upperStarFromPoint X`, the geometric inverse image in the recorded category. |
| Inclusion through the bottom finite intermediate field | `Profinite.padicIntCondensedRingToPadicAlgCl` composes the existing integral-to-rational inclusion, the rational-to-bottom-field inclusion, and `padicSubfieldCondensedRingToPadicAlgCl ℓ ⟨⊥, inferInstance⟩`. The underlying abelian map is `padicIntRingObjToPadicAlgCl`; `coefficientMap ... X` pulls it back. This is the same continuous inclusion through the bottom finite field as in the exhibit. |
| F_n for every natural n, including zero | `tateModuleLevel X ℓ n` is `(Mod.free _).obj (Scheme.proEtaleRootsOfUnitySheaf X (ℓ ^ n))`. Its underlying object is `R_X ⊗ μ`, by the source of `Mod.free`. |
| Tensor the abelian sheaf, with action on the ring factor | Published `CategoryTheory.Mod.freeModObj` acts by `(α_ R R M).inv ≫ μ[R] ▷ M`. It is multiplication on the first factor, with no free-module-on-a-set construction. The published name `Mod.free` supplies the construction called `Mod.freeFunctor` in the exhibit. |
| Successor transition, 1 tensor the ell-power map | `tateModuleTransition` applies `(Mod.free _).map` to the recorded `proEtaleRootsOfUnityTransition` at exponents `ℓ^n` and `ℓ^(n+1)`. Its kernel-lift definition raises units to the quotient of these positive exponents, which is ell. The free functor's source shows its underlying map is `R_X ◁ f`. |
| Composite maps and equal-index identity | `tateModuleSystem := Functor.ofOpSequence (tateModuleTransition X ℓ)`; the existing functor constructs precisely successive composites and identities. |
| Inverse limit T_X over all n at least zero | `tateModule := limit (tateModuleSystem X ℓ)` in internal `R_X`-modules. There is no index offset or positive-index-only replacement. This uses the recorded general `Limits.limit`. |
| Scalar extension L_X over R_X | `tateTwistOne := (Mod.extendScalars (coefficientMap ... X)).obj (tateModule X ℓ)`. The extension is the existing relative tensor with target-ring action on its first factor. |
| Section-ring and module interpretation | Public import of the recorded `sectionModuleEquivalence`, `ringedSiteModules`, mixed-universe sectionwise tensor API, and sheafification-tensor comparison. The existing internal module, relative tensor and scalar extension are used directly; no second category or tensor is defined. The section-module equivalence preserves the underlying abelian sheaves and restrictions. Its section-ring construction uses the internal multiplication and unit. |
| Sheafified sectionwise tensor | The internal relative tensor is the existing balanced coequalizer in abelian sheaves. The dependency's sectionwise tensor and sheafification comparison give the specified module-sheaf interpretation; the module does not choose any comparison isomorphism or assume one as extra data. |
| B_X(0), tensor powers | The zero branch of `tateTwistNat` is `𝟙_ _`, the existing regular B_X module; the successor branch is `tateTwistNat d ⊗ tateTwistOne X ℓ`. |
| Negative twists | The `.negSucc d` branch of `tateTwist` is `(ihom (tateTwistNat X ℓ (d + 1))).obj (𝟙_ _)`, the existing internal module Hom into B_X. The recorded sectionwise `SheafOfModules.homObj` is publicly imported for its sheaf-Hom interpretation. |
| Every integral twist in derived degree zero | `tateTwistDerived X ℓ m := (DerivedCategory.singleFunctor _ 0).obj (tateTwist X ℓ m)`. The source of `singleFunctor` is the single complex followed by localization, with the module in degree zero, zero elsewhere, and zero differentials. |
| No further hypotheses or properties | No finite-field datum, ell-invertibility, trivialization, local-freeness proof, completeness assumption or common-stage identification occurs in any definition. Importing the two-colimit theorem does not impose its Noetherian hypothesis: only its coefficient ring construction is used. |

Dependency declarations and modules read and used or publicly reexported for the
specified interpretations:

- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`, the small-site universe and
  ordinary localization interface. The condensed endpoint uses the recorded internal
  module category, rather than this constant-ring specialization.
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing`:
  `Profinite.isCommMonObj_continuousCoefficientRingObj`; reexports the full existing
  coefficient framework, notably `AlgebraicGeometry.ProEtale.condensedRingObj`,
  `upperStarFromPoint` and its monoidal structure.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`:
  `AlgebraicGeometry.ProEtale.constructibleCocone_isFilteredTwoColimit`; its coefficient
  definitions are `Profinite.padicAlgClRingObj` and the finite-subextension inclusions.
  The theorem itself is not invoked in the definition.
- `Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf`:
  `Scheme.proEtaleRootsOfUnitySheaf` and `Scheme.proEtaleRootsOfUnityTransition`.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `CategoryTheory.Limits.limit`;
  the framework supplies the module category's limits.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`:
  `SheafOfModules.siteSheafTensorRight` and its publicly imported sectionwise tensor
  and scalar-extension constructions.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj`.
- `def-weil-size-convention` is metatheoretic, with no module or declaration;
  the explicit universe choices above implement it.
- `Mathlib.NumberTheory.Padics.PadicNumbers` and `PadicIntegers`: `Padic`, `PadicInt`,
  their existing inclusion and algebra structures, imported through the coefficient API.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence` and
  `sectionRingSheaf`, read from the published server source.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor`:
  `PresheafOfModules.exists_sheafificationTensorIso` and
  `nonempty_sheafTensorSheafificationIso`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.singleFunctor`, reexported by the module
  framework. The last is definitionally the single complex followed by `Q`.
- Additional construction APIs already available in the source:
  `WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian` (`Mod.free`, `freeModObj`),
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension`
  (bottom-field coefficient inclusion),
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`
  (`coefficientMap`, `Mod.extendScalars`), and
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor`
  (the internal module monoidal/closed and derived structures).

Edge cases checked before writing and against the finished definitions:

- `n=0` gives exponent one and the kernel of the identity on units, the zero abelian
  roots-of-unity sheaf. The transition from level one into it exists; it is retained.
- `ℓ^n` and `ℓ^(n+1)` are positive for every n under the prime assumption, including
  n=0. The division exponent of the transition is exactly ell.
- The system is indexed by all `ℕᵒᵖ`; equal-index maps are identities and every
  longer map is a composite, so no compatibility choices are introduced.
- `m=0` gives the tensor unit; `m=1` follows the specified unit-tensor recurrence;
  `m=-1` is Hom of the first positive twist into the unit; every negative integer
  is the `.negSucc` branch, with no missing zero case.
- Empty schemes and schemes of characteristic ell are allowed. No line-bundle or
  local-triviality assertion is made in these definitions, so these cases are not
  excluded or silently assigned a different construction.
- The algebraic-closure coefficient ring uses finite-intermediate-field-valued maps;
  all universes are those of the existing site and coefficient construction.

Searches for an existing exact definition:

- `msearch.py NI def-pur-condensed-tate-twists leanfinder` with query
  “Tate twists on pro-etale site as internal modules over condensed algebraic closure
  of p-adic numbers from inverse limit of roots of unity”: eight hits, including
  BDeRhamPlus, CondensedMod, profinite free/solid and LightCondMod. These have different
  sites or coefficients and do not construct this Tate tower.
- `msearch.py ... loogle '"tateTwist"'`: zero hits.
- `msearch.py ... grep 'tateModuleLevel|tateTwistDerived|padicIntRingObjToPadicAlgCl'`:
  zero Mathlib hits.
- `rg` in the upstream `WeilConjectures` source and `lean/Sheaf` for the construction
  names and condensed/Tate terms: no existing exact definitions. Common-stage Weil
  sheaf twists, group-theoretic Tate modules, and finite-etale twists have different
  objects and are not reused as this endpoint.
- `tools/lean_names_upstream.py show def-pur-condensed-tate-twists`: no attached names
  for this node. Direct focused searches for every new coefficient and endpoint name
  in the upstream and side source trees found no collision.
- The available `Mod.free` source was located and read after the first compile reported
  the archived identifier `Mod.freeFunctor` unavailable. It is exactly ring-times-object
  with multiplication on the ring factor, so the final module imports and uses it.

Validation: `scompile.py NI def-pur-condensed-tate-twists
lean/Sheaf/AlgebraicGeometry/CondensedTateTwists.lean` passed both sandbox and module-name
compilation, with no errors or warnings (5.0 and 4.4 seconds respectively). No library
or global build was run. The required delivery dry run is recorded below after execution.
No `STATEMENT-DISPUTED` issue or node fault was found.

Dry-run result: `deliver2.py NI def-pur-condensed-tate-twists --no-push` printed
`OK (dry run)` at commit `1eb7662b25`: compilation and preflight passed except for
the second-reading section, which the independent reader must write; nothing was pushed.
The node copy differs from the repository only in `lean`. The archived source SHA-256
was independently checked as
`b9554907baced298abbb0648fe084ac9eaffcf576c4e03e6f26a90ff3f0fff2f`, matching the node.

## Second reading by NI

I independently read the node's full statement, all thirteen statement-dependency
nodes and their recorded signatures, the delivered module, and the archived source
exhibit in `coord/reports/maintenance/nt-target-smooth-purity-qbar.md`. This is an
archived-source definition node, not a Stacks statement: its primary source is the
verbatim `TateTwist/ProEtale.lean` exhibit. The source's surrounding binders are
`universe u`, `(X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]`; its implementation notes
explicitly postpone invertibility and local triviality. No field, characteristic,
Noetherian, finite-type or invertibility hypothesis is assumed throughout.

The independent object/hypothesis/clause checklist is:

| Node object, hypothesis or clause | Lean rendering and verdict |
| --- | --- |
| Universes and arbitrary small pro-etale site | `universe u`, `X : Scheme.{u}`, `ProEt.topology X`, `AddCommGrpCat.{u + 1}`. Correct: site objects have universe `u+1`, morphisms `u`; no equality of these universes is imposed. |
| Prime ell and integral/rational coefficient rings | `(ℓ : ℕ) [Fact ℓ.Prime]`, existing `PadicInt` and `Padic`. Correct, with no additional binder. |
| Continuous integral condensed coefficients | Existing `Profinite.continuousMapRingObj ℤ_[ℓ]`. Correct continuous functions with pointwise operations and the framework's universe lift. |
| Algebraic-closure condensed coefficients | Existing `Profinite.padicAlgClRingObj ℓ`. Correct: I read `padicAlgClSubfunctor`, `padicAlgClRingPresheaf` and `padicAlgClCondensedRing`; sections lie in a single finite intermediate field. |
| R_X and B_X by geometric coefficient pullback | `condensedRingObj ... X`, using existing `upperStarFromPoint X`. Correct: I read its definition as `pointUpperStar` followed by inverse image along `toSpecZ X`. |
| Integral coefficient inclusion through the bottom finite field | `padicIntCondensedRingToPadicAlgCl`, `padicIntRingObjToPadicAlgCl`, its `IsMonHom` instance, and `coefficientMap ... X`. Correct: the three existing maps compose the integral inclusion, the algebra map into the bottom field, and that field's inclusion into the finite-extension-valued ring. Pointwise this is the same map as the source's single continuous-map composite. |
| F_n for every natural n | `tateModuleLevel X ℓ n := (Mod.free _).obj (proEtaleRootsOfUnitySheaf X (ℓ ^ n))`. Correct free internal module on the abelian sheaf. |
| Ring action on the first tensor factor | I opened `Mod.freeModObj` and `Mod.free` in `Monoidal/Mod/Abelian.lean`: the object is `R ⊗ M` and its action is associator inverse followed by multiplication on R. Correct; this is not the free module on a set. |
| Successor transition is one tensor the ell-power map | `tateModuleTransition` applies `Mod.free.map` to the recorded kernel transition. Correct: I opened its signature and body, `kernel.lift` of inclusion followed by `(N'/N) • 𝟙`; the positive powers give quotient ell even at n=0. `Mod.free.map` is `R ◁ f`. |
| Arbitrary transition composites and identities | `tateModuleSystem := Functor.ofOpSequence ...`. Correct: no arbitrary transition choices or extra compatibility hypothesis. |
| T_X inverse limit in R_X-modules, all n≥0 | `tateModule := limit (tateModuleSystem X ℓ)`. Correct category and full `ℕᵒᵖ` index. |
| L_X scalar extension and first-factor B_X action | `tateTwistOne := (Mod.extendScalars (coefficientMap ... X)).obj (tateModule X ℓ)`. Correct: I read `extendScalarsObj`, its bimodule left action and balanced-coequalizer description; scalars are extended over R_X. |
| Sectionwise module interpretation, tensor and limit constructions | Public imports of the recorded internal/sectionwise equivalence, `ringedSiteModules`, mixed-universe tensor and sheafification-tensor comparison. Correct: the equivalence reconstructs multiplication/unit and keeps underlying sheaves and restrictions, so the internal limit and balanced tensor have the specified sectionwise/sheafified interpretation. No additional comparison data is assumed. |
| B_X(0) and nonnegative recurrence | `tateTwistNat` has branches `0 => 𝟙_ _` and `d+1 => tateTwistNat d ⊗ tateTwistOne X ℓ`. Correct regular module and tensor over B_X. |
| Negative twists by internal sheaf Hom | `tateTwist` has `.negSucc d => (ihom (tateTwistNat X ℓ (d+1))).obj (𝟙_ _)`. Correct internal module Hom, not global Hom or the underlying abelian Hom. I also read the recorded `SheafOfModules.homObj` signature and sectionwise linear-Hom construction. |
| Integral twist in derived degree zero | `tateTwistDerived X ℓ m := (DerivedCategory.singleFunctor _ 0).obj (tateTwist X ℓ m)`. Correct for every integer. I read Mathlib's `singleFunctor` and `Q_obj_single_obj`: it localizes exactly the single complex. |
| No extra property, identification or hypothesis | None is present in the binders or bodies. Correct: no common-stage category, trivialization, local-freeness, finite-field datum or completeness assertion is substituted. |

Dependency verification: the small-site category and ordinary derived localization
were read in `ProEtaleDerivedCategory`; the coefficient framework is reexported by
`ContinuousCoefficientCommRing`; the finite-extension coefficient definitions are
available through the recorded two-colimit module without using its Noetherian
hypothesis. The roots kernel and transition are exactly the recorded
`Scheme.proEtaleRootsOfUnitySheaf` and `proEtaleRootsOfUnityTransition`. The general
`Limits.limit`, the sectionwise mixed-universe tensor, the recorded sheaf Hom,
`RingedSiteModules` and `SheafificationTensor` signatures were opened and checked.
For the dependency absent in the older clone, I read the complete current published
`InternalAbelianSheafModuleEquivalence` with `scompile.py --source`; its site and
coefficient universes cover this site's `u+1/u` pair. The size convention is
metatheoretic and the p-adic rings and derived category are existing Mathlib objects.
There are no new definition nodes, dependency repairs or statement corrections to audit.

Edge cases: n=0 gives exponent one, the zero roots-of-unity sheaf, and its correct
incoming transition; no positive-index shift discards it. All powers are positive
under primality, including ell=2. The index is fixed nonempty `ℕᵒᵖ`, so no arbitrary
empty-index quantifier is relevant. Zero modules are permitted by the limit, tensor
and internal-Hom constructions. Empty schemes and characteristic ell are admitted,
since no invertibility or line-bundle property is claimed. The zero twist is the
unit, positive twists follow the stated recurrence, and every negative integer is
covered by `negSucc`; in particular -1 is Hom of the first twist into the unit.
All variables and universes are explicitly bound.

Independent searches used different wording from the worker:

- `msearch.py ... leanfinder`: “Cyclotomic sheaf as an inverse limit of multiplicative
  torsion sheaves, base change to condensed algebraic p-adic coefficients and dual
  tensor powers”. Eight hits: BDeRhamPlus, condensed free/solid modules, light
  condensed monoidal categories and cyclotomic characters. Their sites or objects
  differ; none supplies these definitions.
- `msearch.py ... loogle '"tateModule"'`: zero hits.
- `msearch.py ... grep 'cyclotomic|ellAdicSheaf|rootsOfUnitySheaf'`: capped at 25
  hits, mostly cyclotomic fields/characters; I made no absence inference from that
  capped list. An uncapped focused `rg` of Mathlib's `AlgebraicGeometry/Sites`
  returned only `ellAdicSheaf` and its cohomology. I opened its definition: it is
  the continuous integral coefficient sheaf, not this Tate tower or signed twists.
- Independent `rg` over the upstream `WeilConjectures` and project `lean/Sheaf`
  trees for cyclotomic/Tate terms and the new construction names found existing
  group/abelian-variety Tate modules and other coefficient-category twists, but no
  exact condensed pro-etale endpoint or name collision. I read the available
  construction signatures rather than matching their names. A fresh
  `scompile.py --source WeilConjectures.TateTwist.ProEtale` again reported the
  archived module unavailable, so an existing-import binding is not possible.

No semantic mismatch, hollow data, added assumption or omitted clause was found.
The module contains only real-data definitions and the inferred ring-hom instance;
no theorem or proof was added. Every declaration has its source/blueprint docstring,
and there is no proof plan for this definition node (`proof` is empty). The only
change made in this reading is this report section; the Lean and node binding are
retained. The node copy differs from the current base only in `lean`, and its
`lean.statement` is the literal `def tateTwistDerived ...` signature from the file.

Fresh validation: `scompile.py NI def-pur-condensed-tate-twists
lean/Sheaf/AlgebraicGeometry/CondensedTateTwists.lean`, run from the sandbox, passed
both sandbox and library-name compilation in 4.9 and 4.5 seconds, without errors
or warnings. No global build or direct live-library write was performed.

Second-reader dry run: `deliver2.py NI def-pur-condensed-tate-twists --no-push`
printed `OK (dry run): commit 04c00bda04 passes the preflight and compiles; nothing
pushed`. The staged set is exactly the report, item node and one module.
