## Worker report

The module defines `AlgebraicGeometry.RingedSpace.moduleCohomology`.  Given a ringed
space `X`, an `O_X`-module `F` represented by `SheafOfModules (moduleRings X)`, an
injective resolution `I`, and `p : ℕ`, it evaluates each term and differential of
`I.cocomplex` on the top open (`SheafOfModules.evaluation ... (op ⊤)`), forming a
cochain complex in `ModuleCat` over the global section ring.  The definition returns
its `p`-th homology object.  The helper `globalSectionsComplex` is the explicit
complex of global sections.

The ringed-space hypothesis is the explicit `(X : RingedSpace.{u})`; the module
hypothesis is `(F : SheafOfModules.{u} (moduleRings X))`; choosing an injective
resolution is represented by `(I : CategoryTheory.InjectiveResolution F)`; and the
cohomological degree is `(p : ℕ)`.  The conclusion is the module-category object
`ModuleCat ((moduleRings X).obj.obj (op ⊤))` equal to the homology of the global
sections complex.  Resolution independence and right-derived-functor
identification are the accompanying mathematical clauses of the source definition;
this stage introduces the chosen-resolution construction.

Dependencies used: `lem-sc-ringed-space-module-sheaves-enough-injectives`, via
`Sheaf.Topology.RingedSpaceModuleEnoughInjectives` (for the module category and its
injective-resolution context); `def-weil-locally-ringed-space-morphism` and
`def-weil-sheaf-of-modules-category` are represented by Mathlib's `RingedSpace` and
`SheafOfModules`; `lem-sc-ringed-space-module-sheaves-enough-injectives` supplies
`moduleRings`; `def-sp-left-exact-additive` and `def-sp-injective-resolutions` are
represented by Mathlib's `InjectiveResolution` and homology APIs.

Edge cases checked: `p = 0` is accepted by `homology`; arbitrary universe `u` is
retained; no nonemptiness or locality assumption on `X` is added; all differential
indices are handled by the cochain-complex shape and zero-composition law.

Searches: `leanfinder` for “derived global sections cohomology of modules on an
arbitrary ringed space” found only `CategoryTheory.Sheaf.H` and generic sheaf
cohomology; `loogle` for “right derived functor Gamma sheaf module cohomology” had
no hit; grep for `derived.*global sections.*ringed|cohomology.*ringed space` in
Mathlib had no match; `rg` over `WeilConjectures` and project `lean/Sheaf` found no
existing ringed-space module-cohomology definition.

## Earlier second reading (a previous round; superseded)

The module and node were reread together.  The signature introduces exactly X, F, a chosen injective resolution I, and p, and returns the p-th homology of the global-sections cochain complex.  The helper uses the recorded Mathlib cochain-complex and evaluation declarations.  No mismatch was found.

## Second reading by E1

I independently read the node, all five dependency nodes and their declarations, the
module, and the Stacks source in `/home/ubuntu/c1-stacks-review/cohomology.tex`,
Section 20.11 (`section-cohomology-sheaves`, Tag 01DZ), including its ringed-space
paragraph and the following derived-functors section. The source introduces an arbitrary
ringed space, an arbitrary module sheaf, and a resolution; it imposes no locality,
Noetherian, finiteness, field, or nonemptiness hypothesis. The node is correct and
unchanged. The earlier second reading above is superseded; its claim of no mismatch
missed two clauses.

Clause-by-clause checklist:

- Object: the ringed space `(X, O_X)` is `(X : RingedSpace.{u})`. Mathlib's
  `RingedSpace` is `SheafedSpace CommRingCat`, as required by the ringed-space clause
  of `def-weil-locally-ringed-space-morphism`, without any local-ring condition. PASS.
- Object: the module `F` is `SheafOfModules.{u} (moduleRings X)`.
  `moduleRings` is the already landed `AlgebraicGeometry.moduleRings` in
  `Sheaf.Paper.DerivedHomMayerVietoris`: sheaf composition with the forgetful functor
  from commutative rings to rings. This preserves the structure sheaf and its action.
  `SheafOfModules` in Mathlib/Algebra/Category/ModuleCat/Sheaf.lean consists of a
  presheaf of modules with the underlying abelian presheaf a sheaf; its morphisms are
  sectionwise linear. This is exactly `def-weil-sheaf-of-modules-category`. PASS.
- Hypothesis: a chosen injective resolution `F[0] -> I` is
  `(I : CategoryTheory.InjectiveResolution F)`. I read the structure in
  Mathlib/CategoryTheory/Preadditive/Injective/Resolution.lean: its `cocomplex` is
  N-indexed, terms are injective, and `ι` from `single₀ F` is a quasi-isomorphism.
  This matches `def-sp-injective-resolutions`. PASS.
- Hypothesis: the abelian category and enough injectives are supplied by the landed
  `moduleSheaves_abelian_enoughInjectives`, whose signature I read alongside its node.
  Abelian structure already synthesizes from Mathlib's sheafification API; the new
  functor obtains EnoughInjectives from that named theorem internally. There is no
  additional user-supplied instance. PASS.
- Degree: `(p : ℕ)` gives precisely the nonnegative degrees, including zero. PASS.
- Conclusion: `globalSectionsComplex` evaluates `I.cocomplex` at `op ⊤` by
  Mathlib's `Functor.mapHomologicalComplex`; `moduleCohomology` takes its `.homology p`.
  Evaluation at the whole space is global sections, including the induced
  O_X(X)-module structure. Its codomain is `ModuleCat ((moduleRings X).obj.obj (op ⊤))`,
  as explicitly specified in the source. PASS.
- Conclusion: independence was MISSING. Added `moduleCohomology_independent`,
  quantifying over any two resolutions of the same F and asserting a module
  isomorphism in every degree. Independence means isomorphism, not literal equality
  of separately chosen homology objects. PASS after repair.
- Conclusion: right derived functors were MISSING. Added `moduleCohomologyFunctor`
  using Mathlib's `Functor.rightDerived`, the recorded declaration of
  `def-sp-left-exact-additive`, and `moduleCohomology_rightDerived`, comparing its value
  on F with the cohomology of any chosen resolution. I read
  `InjectiveResolution.isoRightDerivedObj` and its surrounding definition: these
  provide precisely the generic comparison for this specialization. PASS after repair.

Edge cases: the empty space and zero sheaf are allowed; no nonempty or nonzero binder
appears. Degree zero is included by N-indexing, with no positivity condition. There
is no characteristic restriction. Universe u is explicitly bound and arbitrary,
matching the landed ringed-space/module-category dependencies; the library's usual
common universe can contain the space, ring sections, and module sections. No finite
index family is introduced; the resolution is indexed by all natural numbers.

Independent searches (2026-10-11, logged through msearch.py):

- LeanFinder: `SheafOfModules evaluation injective resolution homology rightDerived`
  returned generic InjectiveResolution and right-derived-functor declarations,
  but no ringed-space module-cohomology declaration.
- LeanSearch: `Cohomology of sheaves of modules computed by evaluating an injective
  resolution at a terminal object` returned Internal Server Error; recorded as
  unavailable, with no mathematical verdict inferred from the failure.
- Loogle: `"isoRightDerivedObj"` returned the generic comparison and its naturality
  lemmas. Opened RightDerived.lean lines 55--120 and checked its hypotheses.
- Mathlib grep: `moduleCohomology|sectionsFunctor|isoRightDerivedObj|globalSectionsComplex`
  found the generic comparison and a Type-valued sections functor, not this notion.
  The Type-valued functor loses the module structure and is not a substitute.
- Independent rg on all upstream WeilConjectures and project lean/Sheaf for
  `moduleCohomology|cohomology.*[Rr]inged|[Rr]inged.*cohomology` found no existing
  declaration. Checked every newly introduced full name against Mathlib, upstream,
  `dag/lean_names_upstream.json`, and project Lean; none collides.

Other repairs: added the missing license/module header and helper docstring; replaced
handwritten complex construction with Mathlib's existing mapHomologicalComplex API,
removing the original inline proof of differential identities. Evaluation's additive
instance did not synthesize automatically: `moduleGlobalSections_additive` reuses
`inferInstanceAs` for the existing additive forgetful and presheaf-evaluation composite,
without a new theorem or proof. Both new theorem proofs are exactly sorry; their
source-tagged docstrings give complete comparison proofs. No definition contains
sorry data, and no statement was weakened or strengthened. Recorded all declarations
in the node's lean record and kept the main signature verbatim from the file.

There are no new DAG nodes or dependency modules in this delivery. No statement
correction or citer audit is needed. The worker report's description of only a
chosen-resolution construction describes the earlier incomplete module; the final
module now includes the two clauses it called accompanying mathematical clauses.
The full module compiled cleanly on the server through scompile.py (exit 0, no warnings).

## Review fix by R-rmc1416 (stage 2)

One definition per notion (H4/H12). The delivery's main declaration `moduleCohomology X F I p`
took the chosen injective resolution as an argument, so `H^p(X,F)` depended on data and could
not be the declaration later nodes cite; the right derived functor appeared only as the
secondary `moduleCohomologyFunctor`, and global sections was an unnamed inline evaluation.
Restated: `globalSectionsFunctor X : SheafOfModules (moduleRings X) ⥤ ModuleCat O_X(X)`
(evaluation at `⊤`; the ringed-space analogue of H1's `Scheme.Modules.globalSectionsFunctor`,
none existed in lean/Sheaf) with its additivity instance; the main declaration
`moduleCohomology X p := (globalSectionsFunctor X).rightDerived p` (enough injectives from the
landed `moduleSheaves_abelian_enoughInjectives`); `globalSectionsComplex I`;
`moduleCohomology_iso_resolution` (`H^p(X,F) ≅ H^p(Γ(X,I^•))` for every resolution; checked to
close by `InjectiveResolution.isoRightDerivedObj`, left `sorry` as a stage-2 statement) and
`moduleCohomology_independent` on the resolution complexes. `moduleCohomologyFunctor` removed.
Codomain `Mod_{O_X(X)}` as in Stacks 01DZ. For a scheme, `X.Modules` is definitionally
`SheafOfModules (moduleRings X.toRingedSpace)`, so this applies to schemes as well; Mathlib's
`Sheaf.H` / source's `Scheme.Modules.H` are Ext in abelian sheaves and agree only by a theorem.
