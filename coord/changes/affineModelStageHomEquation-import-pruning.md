# affineModelStageHomEquation_of_coherent_objects import pruning

## Reason

The stage Hom equation needs coherent comparison objects and scalar conjugation;
it does not use the constructor of affine comparison data. Import the actual
statement dependency directly and remove the constructor module from this import
path. All existing declarations retain their signatures and visibility.

## Old

```lean
public import Sheaf.AlgebraicGeometry.AffineModelComparisonDataFromHomEquations
```

## New

```lean
public import Sheaf.AlgebraicGeometry.AffineModelCoherentObjectComparisons
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineModelComparisonOfBottomModels | unclaimed | The sole direct importer also imports AffineModelLimitHomEquationOfCoherentObjects, whose public import still provides AffineModelComparisonDataFromHomEquations. Coherent object definitions remain public through the new direct import. No source adaptation is needed. |

The textual import-pruning check passed. There are 436 transitive downstream
modules, but all their paths through this module pass through the sole direct
importer above. That importer still has the constructor module through the limit
Hom equation. This change alters no mathematical definition, target statement or
object comparison, and requires no target meaning review.

## Status

landed 20261014T063823-L-2815810 2026-10-14 (merge of deliver/U2/Sheaf.AlgebraicGeometry.AffineModelStageHomEquationOfCoherentObjects)

## Review packet repair: reviewer X-5b556, point A

The unchanged original direct importer compiled against the delivered item overlay with
`lcompile.py` in 7.6 seconds (exit code 0, no warnings). All 29 snapshot hashes were
compared with the current repository files after this compile and matched.

These are complete, byte-for-byte current original source and node snapshots, read from the
repository on 2026-10-14. They are evidence only; none is an adaptation or a new library module.
The original repository sources remain unchanged. SHA-256 hashes identify the exact bytes.
The snapshot includes the original item, its sole direct importer, all five affine-model
interface modules, and the statement/proof dependencies cited by their node records.
In particular the complete coherent-object source below includes the proved declaration
`AlgebraicGeometry.affineModel_scalarConjugation_nat` and its private proved helpers.

For importer compilation, extract the original importer into a separate `lean/` tree and
use the delivered item compilation as its `.lbuild` overlay with `lcompile.py`. Do not
replace the delivered item with its original snapshot. The sources and records below
allow direct dependency comparison without requiring them in the reviewer clone.

### Original snapshot: `dag/nodes/sec-abelian-varieties/def-pc-scheme.json`

SHA-256: `e4371fca77476096720be08f0053365286287f8af5fe18a3e35f66511e63567f`

```json
{
 "id": "def-pc-scheme",
 "blueprint": {
  "is": "def-pc-scheme",
  "from": null,
  "same_as": null
 },
 "kind": "definition",
 "title": "Schemes",
 "statement": "A *scheme* is a locally ringed space in the sense of Stacks\nProject, Schemes, Definition 26.9.1 (Tag\n[01IJ](https://stacks.math.columbia.edu/tag/01IJ)); $\\mathit{Sch}$ denotes\nthe category of schemes, and a *morphism of schemes* is a morphism\nin $\\mathit{Sch}$. A scheme is *affine* if it is isomorphic to\n$\\operatorname{Spec}(A)$ for a commutative ring $A$; an *open subscheme* of $X$\nis a subscheme whose underlying topological space is open in $X$.",
 "source": {
  "document": "literature/blueprint/master/blueprint/sec-abelian-varieties/sk-def-av-jacobian/def-pc-scheme.md",
  "place": "node def-pc-scheme, order 448",
  "external": [
   {
    "document": "Stacks Project",
    "place": "Tag 01IJ"
   }
  ]
 },
 "stmt_deps": [],
 "proof": [],
 "proof_deps": [],
 "proof_origin": null,
 "mathlib_searches": [
  {
   "tool": "text search of the local Mathlib checkout (0df444a360)",
   "query": "AlgebraicGeometry.Scheme",
   "results": [
    "Mathlib.AlgebraicGeometry.Scheme:42 (structure)"
   ],
   "date": "2026-10-08"
  },
  {
   "tool": "text search of the local Mathlib checkout (0df444a360)",
   "query": "AlgebraicGeometry.Scheme.Hom",
   "results": [
    "Mathlib.AlgebraicGeometry.Scheme:74 (structure)"
   ],
   "date": "2026-10-08"
  }
 ],
 "mathlib_match": [
  "AlgebraicGeometry.Scheme",
  "AlgebraicGeometry.Scheme.Hom"
 ],
 "status": "mathlib",
 "merged_into": null,
 "import_flags": [],
 "blueprint_kind": "definition",
 "blueprint_order": 448,
 "blueprint_uses": [],
 "blueprint_notes": [
  {
   "label": "mathlib",
   "text": "*Mathlib:* `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Hom`. These are basic Mathlib notions used throughout, so they are not mapped as the Lean declarations of this object.",
   "where": "statement"
  }
 ],
 "lean_audit": {
  "master": {
   "state": "none",
   "decls": [],
   "missing": []
  },
  "slopmaster2": {
   "state": "none",
   "decls": [],
   "missing": []
  }
 },
 "chapter": "sec-abelian-varieties",
 "unit": "sk-def-av-jacobian",
 "lean": {
  "module": "Mathlib.AlgebraicGeometry.Scheme",
  "declaration": "AlgebraicGeometry.Scheme",
  "declarations": [
   "AlgebraicGeometry.Scheme",
   "AlgebraicGeometry.Scheme.Hom"
  ],
  "statement": "structure AlgebraicGeometry.Scheme extends LocallyRingedSpace where local_affine : ...",
  "branch": "mathlib",
  "by": "L",
  "date": "2026-10-11",
  "existing": true,
  "note": "Schemes and their morphisms (`X ⟶ Y` = `Scheme.Hom`). Lead note 2026-10-11 11:42 UTC: recorded by bookkeeping agent B-1137 of L; name and signature read in the pinned Mathlib (0df444a360) of the slopmaster2 checkout."
 }
}
```

### Original snapshot: `dag/nodes/sec-picard-framework/def-pc-affine-model-comparison-data.json`

SHA-256: `08f47a716ffb54c9d54ae395b2e222975099ef0e9ee44c51dcbdfa400c722af3`

```json
{
 "source": {
  "document": "literature/stacks-project/perfect.tex",
  "place": "Tag 09RE affine Hom comparison; Tag 08DW(2), notation for coherent object comparisons and naturality on sheafified chain maps"
 },
 "stmt_deps": [
  "def-pc-scheme",
  "def-pc-derived-category",
  "def-pc-derived-pullback",
  "def-pc-complex-scalar-extension-hom",
  "lem-pc-perfect-hom-transport"
 ],
 "mathlib_searches": [
  {
   "tool": "leanfinder",
   "query": "Natural equivalence of derived Hom sets for affine bounded projective complexes compatible with extension of scalars and scheme pullback",
   "results": "Hits: CategoryTheory.ProjectiveResolution.isoExt, CategoryTheory.ProjectiveResolution.extMk_hom, CategoryTheory.Abelian.Ext.homLinearEquiv, CategoryTheory.Abelian.Ext.homEquiv, CochainComplex.HomComplex.CohomologyClass.bijective_toSmallShiftedHom_of_isKProjective, CategoryTheory.ProjectiveResolution.extEquivCohomologyClass_symm_mk_hom, AlgebraicGeometry.AffineSpace.homOverEquiv, AlgebraicGeometry.AffineSpace.homOverEquiv_apply",
   "date": "2026-10-13",
   "verdict": "No combined comparison statement; existing generic constructions reused where applicable."
  },
  {
   "tool": "loogle",
   "query": "ModuleCat.extendScalars",
   "results": "Hits: ModuleCat.extendScalars, ModuleCat.instIsLeftAdjointExtendScalars, ModuleCat.extendRestrictScalarsAdj, ModuleCat.extendScalarsId, ModuleCat.ExtendRestrictScalarsAdj.Counit.map, ModuleCat.ExtendRestrictScalarsAdj.Unit.map, ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars, ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars",
   "date": "2026-10-13",
   "verdict": "No combined comparison statement; existing generic constructions reused where applicable."
  },
  {
   "tool": "loogle",
   "query": "Under.pushout",
   "results": "loogle: unknown identifier 'Under.pushout'",
   "date": "2026-10-13",
   "verdict": "No combined comparison statement; existing generic constructions reused where applicable."
  },
  {
   "tool": "leanfinder",
   "query": "Commutative ring diagram obtained by pushing out a directed diagram along a map from its initial stage",
   "results": "Hits: CategoryTheory.SmallObject.attachCellsιFunctorObj, CategoryTheory.SmallObject.functorObj, CategoryTheory.SmallObject.πFunctorObj, CategoryTheory.SmallObject.ιFunctorObj, CategoryTheory.SmallObject.functorObj_isPushout, CategoryTheory.SmallObject.ρFunctorObj, CommRingCat.pushoutCoconeIsColimit, HomotopicalAlgebra.AttachCells",
   "date": "2026-10-13",
   "verdict": "No combined comparison statement; existing generic constructions reused where applicable."
  },
  {
   "tool": "grep",
   "query": "affineBaseChangeRingDiagram|exists_affineBaseChangeModelComparisonIsos|exists_affineTildeHomEquiv",
   "results": "Hits: ",
   "date": "2026-10-13",
   "verdict": "No combined comparison statement; existing generic constructions reused where applicable."
  },
  {
   "tool": "leansearch",
   "query": "Affine derived scalar extension comparison natural on chain maps",
   "results": "service unavailable: Internal Server Error",
   "date": "2026-10-13",
   "verdict": "unavailable"
  },
  {
   "tool": "leansearch",
   "query": "Pushout ring diagram on the upper tail of a preorder",
   "results": "service unavailable: Internal Server Error",
   "date": "2026-10-13",
   "verdict": "unavailable"
  },
  {
   "tool": "grep",
   "query": "affineModelComparisonData|Affine.*ComparisonData|affine.*Model.*Data",
   "results": "Returned zero hits in the existing library; the proposition names the exact comparison formula of the two new lemmas.",
   "date": "2026-10-13",
   "verdict": "no match"
  }
 ],
 "mathlib_match": null,
 "status": "split",
 "blueprint": {
  "is": null,
  "from": {
   "node": null,
   "place": "lem-pc-affine-specified-model-chain-comparison, proof steps 2–3: object comparisons and sheafified-chain-map coherence",
   "via": [
    "lem-pc-affine-specified-model-chain-comparison"
   ]
  },
  "same_as": []
 },
 "chapter": "sec-picard-framework",
 "unit": "sk-thm-picard-semicon",
 "id": "def-pc-affine-model-comparison-data",
 "kind": "definition",
 "title": "Coherent affine model comparison data",
 "proof": [],
 "proof_deps": [],
 "proof_origin": null,
 "created": {
  "by": "worker",
  "item": "Sheaf.AlgebraicGeometry.AffineSpecifiedModelChainComparison",
  "date": "2026-10-14",
  "group": "M2"
 },
 "statement": "Let $I$ be a preorder, $R:I\\to\\mathrm{CommRing}$ a diagram, $c$ a cocone, $i\\in I$, $Y$ affine [def-pc-scheme], and $s:Y\\to\\operatorname{Spec}R(i)$. Assume scheme-derived categories with Hom universe $w$ [def-pc-derived-category], and let $P,Q\\in D(\\mathcal O_Y)$. For any diagram $F:\\{j\\mid i\\le j\\}\\to\\mathrm{CommRing}$ a cocone $C$ on $F$, and complexes $E,K$ over $F(i)$, set $E_j=F(j)\\otimes_{F(i)}E$ and $K_j=F(j)\\otimes_{F(i)}K$, and similarly $E_\\infty,K_\\infty$ over $C.pt$. Let $T_A$ be termwise tilde on complexes over $A$. Define affineModelComparisonData to be the following proposition. There exist equivalences $d_j:D(\\mathcal O_{\\operatorname{Spec}F(j)})\\simeq D(\\mathcal O_{Y\\times_{\\operatorname{Spec}R(i)}\\operatorname{Spec}R(j)})$ and $d_\\infty:D(\\mathcal O_{\\operatorname{Spec}C.pt})\\simeq D(\\mathcal O_{Y\\times_{\\operatorname{Spec}R(i)}\\operatorname{Spec}c.pt})$, and isomorphisms $\\alpha E_j:d_j(\\mathsf Q(T_{F(j)}E_j))\\cong Lp_j^*P$, $\\alpha K_j:d_j(\\mathsf Q(T_{F(j)}K_j))\\cong Lp_j^*Q$, $\\beta E:d_\\infty(\\mathsf Q(T_{C.pt}E_\\infty))\\cong Lp_\\infty^*P$, and $\\beta K$ analogously. Here $\\mathsf Q$ is localization and $p_j,p_\\infty$ are the first pullback projections [def-pc-derived-pullback]. For each chain map $f:E_j\\to K_j$, let $C_j(f)$ be the left-to-right composite $\\alpha E_j^{-1}$, $d_j(\\mathsf Q(T_{F(j)}f))$, $\\alpha K_j$, and define $C_\\infty$ analogously. These must satisfy $C_k(\\operatorname{scalarExtensionHom}_{j,k}(f))=\\operatorname{perfectStageMap}_{j,k}(C_j(f))$ and $C_\\infty(\\operatorname{scalarExtensionHom}_{j,\\infty}(f))=\\operatorname{perfectLimitMap}_{j}(C_j(f))$, with the exact ring-map equality witnesses and pinned geometric maps of [def-pc-complex-scalar-extension-hom] and [lem-pc-perfect-hom-transport]. This is a proposition defined by this formula, with no data selected from an unproved theorem and no module-derived category assumption. The generic cocone C need not be colimiting; the supplied comparison data contain its two compatibility equations. In the specified affine model application C is the actual colimit cocone of F.",
 "lean": {
  "existing": false,
  "module": "Sheaf.AlgebraicGeometry.AffineModelComparisonData",
  "file": "lean/Sheaf/AlgebraicGeometry/AffineModelComparisonData.lean",
  "declaration": "AlgebraicGeometry.affineModelComparisonData",
  "statement": "def affineModelComparisonData\n    {I : Type u} [Preorder I]\n    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)\n    (i : I) (Y : Scheme.{u}) [IsAffine Y] (s : Y ⟶ Spec (R.obj i))\n    [∀ Z : Scheme.{u},\n      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]\n    (P Q : schemeDerivedCategory Y)\n    (F : Set.Ici i ⥤ CommRingCat.{u}) (C : Cocone F)\n    (E K : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ)\n    : Prop",
  "branch": "sheaf-dag",
  "by": "M2",
  "date": "2026-10-14"
 },
 "reviewed": {
  "date": "2026-10-13",
  "by": "L",
  "reviewer": "COMPILER",
  "group": "M2",
  "result": "pass",
  "landing": "20261013T190145-L-3217805",
  "kind": "interface",
  "note": "new node of a stage-3 delivery, read against its source by the reviewer"
 },
 "reviewed_proof": {
  "date": "2026-10-13",
  "by": "L",
  "reviewer": "COMPILER",
  "group": "M2",
  "result": "pass",
  "landing": "20261013T190145-L-3217805",
  "kind": "interface",
  "note": "AUTO: proofs only; landed in a batch after the tools' static checks; compiled with the probe by the group's delivery tool, verified by the global build (compile, axioms, sorry, 60 s per file); not read by a reviewer (stage 3, decision of the human 2026-10-12)"
 }
}
```

### Original snapshot: `dag/nodes/sec-picard-framework/def-pc-complex-scalar-extension-hom.json`

SHA-256: `5aa2846c8abfeac852e1254882814a24017777a979ae5ec8967b89601727cef1`

```json
{
 "id": "def-pc-complex-scalar-extension-hom",
 "kind": "definition",
 "title": "Scalar extension of maps between base-extended complexes",
 "status": "split",
 "statement": "Let R, S, T be commutative rings, f:R→S, g:S→T, h:R→T ring homomorphisms with h=g∘f, and P,Q cochain complexes of R-modules (the one-point-site specialization of [def-pc-cochain-complex-modules]). For a chain map a:S⊗_R P→S⊗_R Q, define its scalar extension to T, as a map T⊗_R P→T⊗_R Q, by applying T⊗_S− termwise to a and conjugating by the canonical composite scalar-extension comparison of [def-pod-ring-scalar-extension], using h=g∘f to identify the direct extensions. The comparison is the one induced by uniqueness of left adjoints to restriction of scalars.",
 "stmt_deps": [
  "def-pc-cochain-complex-modules",
  "def-pod-ring-scalar-extension"
 ],
 "source": {
  "document": "literature/stacks-project/perfect.tex",
  "place": "Derived Categories of Schemes, Tag 09RE, lemma-descend-homomorphisms, affine scalar-extension comparison"
 },
 "proof": [],
 "proof_deps": [],
 "proof_origin": null,
 "mathlib_match": null,
 "mathlib_searches": [
  {
   "tool": "leansearch",
   "query": "canonical scalar extension of chain maps between base extended complexes",
   "results": "Service unavailable: Internal Server Error.",
   "date": "2026-10-11",
   "verdict": "unavailable; used LeanFinder, Loogle and grep"
  },
  {
   "tool": "leanfinder",
   "query": "canonical extension of scalars of chain map between two complexes extended from a base ring",
   "results": "HomologicalComplex.extendMap concerns shape embeddings; ModuleCat.ExtendScalars.map' concerns a single scalar extension.",
   "date": "2026-10-11",
   "verdict": "no exact composite chain-map comparison"
  },
  {
   "tool": "loogle",
   "query": "ModuleCat.extendScalarsComp",
   "results": "Canonical associativity at module-functor level; NatIso.mapHomologicalComplex gives its complex-level components.",
   "date": "2026-10-11",
   "verdict": "components exist; transported map not a named declaration"
  },
  {
   "tool": "grep",
   "query": "scalarExtensionHom|baseChangeHom|extendScalarsComp in dag/nodes, Mathlib homology, WeilConjectures and lean/Sheaf; blueprint_refs.py search scalar extension",
   "results": "No transported chain-map declaration. RingTensorCohomology contains a module comparison; def-pod-ring-scalar-extension supplies general scalar extension and its associativity.",
   "date": "2026-10-11",
   "verdict": "no exact notion; reuse components and cite existing scalar-extension node"
  }
 ],
 "created": {
  "by": "worker",
  "item": "lem-pc-affine-perfect-hom-colimit",
  "date": "2026-10-11",
  "group": "J1"
 },
 "blueprint": {
  "is": null,
  "from": {
   "node": "lem-pc-rf-perfect-base-change",
   "place": "Affine scalar-extension maps used by the Hom-colimit comparison",
   "via": [
    "lem-pc-affine-perfect-hom-colimit",
    "lem-pc-perfect-descend-morphisms",
    "lem-pc-perfect-complex-descent",
    "lem-pc-noetherian-approximation-data",
    "lem-pc-proper-support-perfect-direct-image"
   ]
  },
  "same_as": []
 },
 "lean_audit": {
  "master": {
   "state": "none",
   "decls": [],
   "missing": []
  },
  "slopmaster2": {
   "state": "none",
   "decls": [],
   "missing": []
  }
 },
 "chapter": "sec-picard-framework",
 "unit": "sk-thm-picard-semicon",
 "lean": {
  "module": "Sheaf.Algebra.Homology.ScalarExtensionHom",
  "declaration": "CochainComplex.scalarExtensionHom",
  "file": "lean/Sheaf/Algebra/Homology/ScalarExtensionHom.lean",
  "statement": "def scalarExtensionHom {R S T : Type u₁} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) (h : R →+* T) (hc : h = g.comp f) (P Q : CochainComplex (ModuleCat.{u₁} R) ℤ) (a : ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj P ⟶ ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj Q) : ((ModuleCat.extendScalars h).mapHomologicalComplex (.up ℤ)).obj P ⟶ ((ModuleCat.extendScalars h).mapHomologicalComplex (.up ℤ)).obj Q",
  "branch": "sheaf-dag",
  "by": "J1",
  "date": "2026-10-11",
  "existing": false
 },
 "reviewed": {
  "date": "2026-10-11",
  "by": "L",
  "reviewer": "R-aph",
  "group": "J1",
  "result": "fix",
  "note": "new definition node of a stage-2 delivery, read against its source by the reviewer"
 },
 "reviewed_lean": {
  "date": "2026-10-11",
  "by": "L",
  "reviewer": "R-aph",
  "group": "J1",
  "result": "fix",
  "note": "Statement matches node clause by clause (stage tail Set.Ici i0, E_i/K_i/E/K by termwise extendScalars along F.map / colimit.iota, bounded finite projective E0,K0); H/ident/c/e are pinned by htransition/hcanonical on all chain representatives (bounded projective source: Q.map full), satisfiable; removed hollow [HasColimit F] (STATE FILTERED COLIMITS OF RINGS, I : Type u). New node def-pc-complex-scalar-extension-hom: transport of a chain map along extendScalarsComp and h = g.comp f; no Mathlib/slopmaster2/landed declaration gives it (RingTensorCohomology.extendCompIso is the algebraMap-tower functor iso, not the map transport; U1's filteredScalarComplex is termwise extension, no overlap); check_dag clean on the branch tree; no existing node changed besides the item's stmt_deps/lean."
 }
}
```

### Original snapshot: `dag/nodes/sec-picard-framework/def-pc-derived-category.json`

SHA-256: `f64f2ea70e04342c9dee0074ecd19894f5cb048197ad5193da9caf333bf636e4`

```json
{
 "id": "def-pc-derived-category",
 "blueprint": {
  "is": "def-pc-derived-category",
  "from": null,
  "same_as": []
 },
 "kind": "definition",
 "title": "The derived category of $\\mathcal{O}_X$-modules",
 "statement": "Let $X$ be a scheme [def-pc-scheme]. Apply the derived-category construction [def-weil-abstract-derived-category] to the abelian category of sheaves of $\\mathcal O_X$-modules [def-weil-sheaf-of-modules-category]; denote the result by $D(\\mathcal O_X)$. The category $D_{\\mathrm{QCoh}}(\\mathcal O_X)$ is the full subcategory consisting of objects whose cohomology sheaves are quasi-coherent [pqf-def-coherent].",
 "source": {
  "document": "literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-coherence/def-pc-derived-category.md",
  "place": "node def-pc-derived-category, order 643"
 },
 "stmt_deps": [
  "def-pc-scheme",
  "def-weil-abstract-derived-category",
  "def-weil-sheaf-of-modules-category",
  "pqf-def-coherent"
 ],
 "proof": [],
 "proof_deps": [],
 "proof_origin": null,
 "mathlib_searches": [
  {
   "tool": "leanfinder",
   "query": "derived category of sheaves of O_X-modules and full subcategory whose cohomology sheaves are quasi-coherent",
   "results": "DerivedCategory (Mathlib/Algebra/Homology/DerivedCategory/Basic), DerivedCategory.Q (same), DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp (same), SheafOfModules.isQuasicoherent (Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent); no declaration combines the O_X-module specialization with the quasi-coherent-cohomology full subcategory",
   "date": "2026-10-11",
   "verdict": "no match; generic components only"
  },
  {
   "tool": "loogle",
   "query": "DerivedCategory, Sheaf, QuasiCoherent",
   "results": "0 hits; unknown identifier 'Sheaf'",
   "date": "2026-10-11",
   "verdict": "no match"
  },
  {
   "tool": "grep",
   "query": "DerivedCategory|quasi.?coherent [Mathlib/Algebra/Homology/DerivedCategory]",
   "results": "0 hits in Mathlib/Algebra/Homology/DerivedCategory",
   "date": "2026-10-11",
   "verdict": "no match"
  },
  {
   "tool": "leansearch",
   "query": "derived category sheaves modules quasi-coherent cohomology",
   "results": "service unavailable: Internal Server Error",
   "date": "2026-10-11",
   "verdict": "unavailable"
  },
  {
   "tool": "leanfinder",
   "query": "full subcategory of derived category with quasi-coherent cohomology sheaves",
   "results": "DerivedCategory, DerivedCategory.IsGE, DerivedCategory.IsLE and related generic support declarations; no quasi-coherent full-subcategory declaration",
   "date": "2026-10-11",
   "verdict": "no match; generic components only"
  },
  {
   "tool": "loogle",
   "query": "DerivedCategory.homologyProperty",
   "results": "0 hits; unknown identifier 'DerivedCategory.homologyProperty'",
   "date": "2026-10-11",
   "verdict": "no match"
  },
  {
   "tool": "grep",
   "query": "homologyProperty|DerivedCategory.*FullSubcategory|quasi.?coherent [Mathlib/Algebra/Homology/DerivedCategory]",
   "results": "0 hits in Mathlib/Algebra/Homology/DerivedCategory",
   "date": "2026-10-11",
   "verdict": "no match"
  }
 ],
 "mathlib_match": null,
 "status": "split",
 "merged_into": null,
 "import_flags": [],
 "blueprint_kind": "definition",
 "blueprint_order": 643,
 "blueprint_uses": [
  "def-pc-scheme",
  "def-weil-abstract-derived-category"
 ],
 "uses_not_cited": [
  "def-pc-scheme",
  "def-weil-abstract-derived-category"
 ],
 "lean_audit": {
  "master": {
   "state": "none",
   "decls": [],
   "missing": []
  },
  "slopmaster2": {
   "state": "none",
   "decls": [],
   "missing": []
  }
 },
 "chapter": "sec-picard-framework",
 "unit": "sk-thm-picard-coherence",
 "split_report": {
  "date": "2026-10-11",
  "item": "def-pc-derived-category",
  "worker": "stage1",
  "summary": "Split the imported definition without creating helper nodes. The abstract derived category is supplied by the existing def-weil-abstract-derived-category Mathlib leaf, and the sheaf-of-O_X-modules category is supplied by the existing definition dependency; the quasi-coherent derived subcategory is a defining full-subcategory clause rather than a separate theorem. No exact project declaration exists in the source checkout. Mathlib searches found only the generic DerivedCategory and SheafOfModules.isQuasicoherent components, not the combined definition.",
  "blueprint": "The item is the blueprint node def-pc-derived-category itself (order 643); its statement realizes the definition of D(O_X) and the full subcategory D_QCoh(O_X) by the clause naming objects whose cohomology sheaves are quasi-coherent."
 },
 "reviewed": {
  "date": "2026-10-10",
  "by": "L",
  "reviewer": "R-ddc2924",
  "group": "M1",
  "result": "pass",
  "note": "mechanical checks by tools/merge_delivery.py; mathematics reviewed in full by R-ddc2924 (reviewer sub-agent of L); spot-checked: E7/C4: statement diffed against sheaf-dag: text identical apart from four added citations [def-pc-scheme, def-weil-abstract-derived-category, def-weil-sheaf-of-modules-category, pqf-def-coherent]; no mathematical clause changed, so citers (lem-pc-perfect-generator-exists, lem-pc-qcqs-derived-direct-image-right-adjoint, lem-pc-derived-mayer-vietoris-triangle, lem-pc-affine-qcoh-derived-equivalence) unaffected; derived-category construction cites def-weil-abstract-derived-category (class b reuse); abelian category of O_X-modules is the clause of def-weil-sheaf-of-modules-category; quasi-coherent is clause 1 of pqf-def-coherent (Tag 01BE), no cycle; no triangulated-subcategory claim (Tag 08DL-area) smuggled in; def-pc-derived-direct-image and def-pc-global-derived-rhom consistent. Mathlib grep DerivedCategory+Scheme/SheafOfModules/Modules: 0 hits, not a leaf. FIX more, RETURN less: none needed."
 },
 "lean": {
  "module": "Sheaf.AlgebraicGeometry.DerivedCategory",
  "declaration": "AlgebraicGeometry.schemeDerivedCategory",
  "declarations": [
   "AlgebraicGeometry.schemeDerivedCategory",
   "AlgebraicGeometry.schemeDerivedQCohProperty",
   "AlgebraicGeometry.schemeDerivedQCohCategory"
  ],
  "file": "lean/Sheaf/AlgebraicGeometry/DerivedCategory.lean",
  "statement": "abbrev schemeDerivedCategory (X : Scheme.{u}) [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] : Type _",
  "branch": "sheaf-dag",
  "by": "E1",
  "date": "2026-10-11",
  "existing": false,
  "fixed_by": "R-pdc1201"
 },
 "reviewed_lean": {
  "date": "2026-10-11",
  "by": "L",
  "reviewer": "R-pdc1201",
  "group": "E1",
  "result": "fix",
  "note": "scheme X = Scheme.{u}; Mod(O_X) = SheafOfModules (moduleRings X.toRingedSpace) (shared carrier; X.Modules gives a second HasDerivedCategory, tested); D(O_X) = DerivedCategory with shared HasDerivedCategory.{w} binder; D_QCoh = FullSubcategory of forall n:Z IsQuasicoherent (homologyFunctor n).obj K; citers checked: IsCoherent on H^n, overFunctor.mapDerivedCategory, RingedSpace.derivedProducts, D_QCoh obj"
 }
}
```

### Original snapshot: `dag/nodes/sec-picard-framework/def-pc-derived-pullback.json`

SHA-256: `be5694887a7b9eb5ea32a0ce8bdb4d81a9870a5949067bed1c4c329e757aa075`

```json
{
 "id": "def-pc-derived-pullback",
 "blueprint": {
  "is": "def-pc-derived-pullback",
  "from": null,
  "same_as": []
 },
 "kind": "definition",
 "title": "Derived pullback of modules on schemes",
 "statement": "Let $g:T\\to S$ be a morphism of schemes [def-pc-scheme], with ring map $g^\\sharp:g^{-1}\\mathcal O_S\\to\\mathcal O_T$, and let $D(\\mathcal O_S)$, $D(\\mathcal O_T)$ be the derived categories of [def-pc-derived-category]. The *derived pullback* $Lg^*:D(\\mathcal O_S)\\to D(\\mathcal O_T)$ is the composite of the termwise inverse image $g^{-1}:D(\\mathcal O_S)\\to D(g^{-1}\\mathcal O_S)$ [def-weil-pbc-topological-inverse-image] (well defined because $g^{-1}$ is exact) with the derived change of rings along $g^\\sharp$ on the site of open subsets of $T$ [lem-pur-derived-change-of-rings]:\n\n$$\nLg^*E=\\mathcal O_T\\otimes^{\\mathbf L}_{g^{-1}\\mathcal O_S}g^{-1}E.\n$$\n\nIt is computed by a K-flat resolution: for every K-flat resolution $\\mathcal P^\\bullet\\to E$ of a complex of $\\mathcal O_S$-modules [def-pc-kflat-complex] (one exists by [lem-pc-kflat-resolution]), $g^{-1}\\mathcal P^\\bullet\\to g^{-1}E$ is a K-flat resolution over $g^{-1}\\mathcal O_S$, and $Lg^*E\\cong g^*\\mathcal P^\\bullet=\\mathcal O_T\\otimes_{g^{-1}\\mathcal O_S}g^{-1}\\mathcal P^\\bullet$, the termwise module pullback [def-pc-module-pullback] (sheaf tensor product [def-pur-sheaf-tensor-product], as a complex [def-pc-tensor-complex-sheaves]), canonically in $D(\\mathcal O_T)$ and independently of the resolution.",
 "source": {
  "document": "literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-semicon/def-pc-derived-pullback.md",
  "place": "node def-pc-derived-pullback, order 665"
 },
 "stmt_deps": [
  "def-pc-derived-category",
  "def-pc-scheme",
  "def-weil-pbc-topological-inverse-image",
  "lem-pur-derived-change-of-rings",
  "def-pc-kflat-complex",
  "lem-pc-kflat-resolution",
  "def-pc-module-pullback",
  "def-pur-sheaf-tensor-product",
  "def-pc-tensor-complex-sheaves"
 ],
 "proof": [
  {
   "text": "Obtain the additive exact inverse-image functor I and its K-flat resolution clause from the inverse-image preservation theorem.",
   "uses": [
    "lem-pc-inverse-image-exact-kflat-resolution"
   ],
   "elementary": false
  },
  {
   "text": "Take E to be the recorded tensor pullback. Its adjunction with pushforward makes it a left adjoint, so it preserves finite colimits and is additive. Its induced homotopy functor is triangulated by the additive mapping-cone construction, and so is its composite F with the target derived localization.",
   "uses": [
    "def-pc-module-pullback"
   ],
   "elementary": true
  },
  {
   "text": "Let C consist of homotopy-category objects represented by K-flat complexes. Every homotopy object is represented by a complex G. Choose a K-flat resolution P -> G; quotienting gives a quasi-isomorphism from an object of C. For any morphism between two objects of C, fullness of the homotopy quotient gives a representative complex map. If it is a quasi-isomorphism, tensor pullback preserves that property by the preservation theorem; the target derived localization therefore inverts it.",
   "uses": [
    "lem-pc-kflat-resolution",
    "lem-pc-tensor-pullback-kflat-quasi-iso"
   ],
   "elementary": false
  },
  {
   "text": "Apply the resolving-class left-derived theorem to F and C. It supplies L, the universal counit, a shift-compatible triangulated structure, and a counit isomorphism on C. Every K-flat complex P represents an object of C, giving the required final clause. Combine these with I and the definitional object and map formulas for E.",
   "uses": [
    "lem-pur-left-derived-from-kflat-class"
   ],
   "elementary": false
  }
 ],
 "proof_deps": [
  "lem-pc-inverse-image-exact-kflat-resolution",
  "def-pc-module-pullback",
  "lem-pc-kflat-resolution",
  "lem-pc-tensor-pullback-kflat-quasi-iso",
  "lem-pur-left-derived-from-kflat-class"
 ],
 "proof_origin": {
  "by": "document",
  "document": "literature/stacks-project/cohomology.tex",
  "place": "Lemma Tag 06YJ (lemma-derived-base-change), proof: direct resolving-class construction of LF"
 },
 "mathlib_searches": [
  {
   "tool": "leanfinder",
   "query": "left derived pullback of sheaves on schemes, derived tensor product with inverse image",
   "results": "AlgebraicGeometry.Scheme.Modules.pullback (Mathlib/AlgebraicGeometry/Modules/Sheaf), pullbackPushforwardAdjunction, and related underived pullback declarations",
   "date": "2026-10-11",
   "verdict": "no match: underived module pullback only"
  },
  {
   "tool": "loogle",
   "query": "leftDerivedFunctor, leftDerivedUpperStar, derived tensor product",
   "results": "unknown identifier 'leftDerivedFunctor'",
   "date": "2026-10-11",
   "verdict": "unavailable"
  },
  {
   "tool": "grep",
   "query": "leftDerivedUpperStar|derivedUpperStar|K-flat in Mathlib/CategoryTheory/DerivedCategory",
   "results": "none",
   "date": "2026-10-11",
   "verdict": "no match"
  },
  {
   "tool": "leansearch",
   "query": "derived pullback Lg star computed as tensor product of structure sheaf with inverse image",
   "results": "service unavailable: Internal Server Error",
   "date": "2026-10-11",
   "verdict": "unavailable"
  },
  {
   "tool": "leanfinder",
   "query": "total left derived functor of exact inverse image functor on sheaves",
   "results": "CategoryTheory.Functor.instIsLeftDerivedFunctorTotalLeftDerivedTotalLeftDerivedCounit and generic localization-derived-functor declarations",
   "date": "2026-10-11",
   "verdict": "generalization: generic derived-functor infrastructure, not this scheme-module construction"
  },
  {
   "tool": "loogle",
   "query": "Functor.leftDerivedFunctor, DerivedCategory",
   "results": "unknown identifier 'Functor.leftDerivedFunctor'",
   "date": "2026-10-11",
   "verdict": "unavailable"
  },
  {
   "tool": "grep",
   "query": "leftDerivedFunctor|mapDerivedCategory|derived.*tensor in Mathlib/Algebra/Homology",
   "results": "Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean:36 mapDerivedCategory; no derived tensor product or scheme-module derived pullback",
   "date": "2026-10-11",
   "verdict": "no match: exact-functor derived-category infrastructure only"
  },
  {
   "tool": "leansearch",
   "query": "total left derived functor inverse image sheaf modules",
   "results": "service unavailable: Internal Server Error",
   "date": "2026-10-11",
   "verdict": "unavailable"
  }
 ],
 "mathlib_match": null,
 "status": "split",
 "merged_into": null,
 "import_flags": [],
 "blueprint_kind": "definition",
 "blueprint_order": 665,
 "blueprint_uses": [
  "def-pc-derived-category",
  "def-pc-scheme",
  "def-weil-derived-tensor"
 ],
 "uses_not_cited": [
  "def-pc-derived-category",
  "def-pc-scheme",
  "def-weil-derived-tensor"
 ],
 "lean_audit": {
  "master": {
   "state": "none",
   "decls": [],
   "missing": []
  },
  "slopmaster2": {
   "state": "none",
   "decls": [],
   "missing": []
  }
 },
 "chapter": "sec-picard-framework",
 "unit": "sk-thm-picard-semicon",
 "split_report": {
  "date": "2026-10-11",
  "item": "def-pc-derived-pullback",
  "worker": "stage1",
  "summary": "Checked the imported definition against its blueprint source and the generic ringed-site definitions already present in the DAG. No sorry-free project declaration states this general derived pullback definition exactly; existing Lean declarations concern etale sheaves with specific coefficient categories. Replaced the imported pro-etale-specific derived-tensor dependency with the generic module pullback, K-flat complex, K-flat resolution, sheaf tensor, and tensor-complex nodes that state the notions used by the formula. No new node was necessary.",
  "blueprint": "The item is itself blueprint node def-pc-derived-pullback (order 665); its statement is realized directly, with no proof steps because it is a definition."
 },
 "tool_uses": [
  "lem-pur-derived-change-of-rings",
  "lem-pc-kflat-pullback-preservation"
 ],
 "reviewed": {
  "date": "2026-10-10",
  "by": "L",
  "reviewer": "R-ddp1839",
  "group": "F1",
  "result": "pass",
  "note": "mechanical checks by tools/merge_delivery.py; mathematics reviewed in full by R-ddp1839 (reviewer sub-agent of L); spot-checked: Read packet; checked no cycle (stmt/proof deps exclude derived-pullback-composition and derived-adjoint; lem-pc-kflat-pullback-preservation and lem-pur-derived-change-of-rings do not depend on this item); checked Stacks 06YI/06YJ/06YC/06YG text. FIX more, RETURN less: C1/E7 the delivered definition asserted 'computed by a K-flat resolution' with no argument for independence of the resolution and left ambiguous which complex is resolved; restated precisely as Lg^* = L(g^sharp)^* o g^{-1} with the derived change of rings of lem-pur-derived-change-of-rings (generic tool, other unit) and added three proof steps (g^{-1} exact via lem-weil-pbc-topological-inverse-image-stalk; derived change of rings; g^{-1}P K-flat over g^{-1}O_S via lem-pc-kflat-pullback-preservation (06YC) on (T,g^{-1}O_S)->(S,O_S), so Lg^*E = g^*P independently of P, Stacks 06YJ). Dropped the unsupported phrase 'the left derived functor' (E7). Second reading by F1 missed this.; 1 file(s) fixed by the reviewer"
 },
 "lean": {
  "module": "Sheaf.AlgebraicGeometry.DerivedPullback",
  "declaration": "AlgebraicGeometry.derivedPullback",
  "file": "lean/Sheaf/AlgebraicGeometry/DerivedPullback.lean",
  "statement": "def derivedPullback {T S : Scheme.{u}} (g : T ⟶ S) [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))] [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))] : schemeDerivedCategory S ⥤ schemeDerivedCategory T",
  "branch": "sheaf-dag",
  "by": "K1",
  "date": "2026-10-11",
  "existing": false,
  "declarations": [
   "AlgebraicGeometry.exists_derivedPullback",
   "AlgebraicGeometry.derivedPullback"
  ],
  "note": "The chosen functor satisfies the left-derived universal property for the recorded tensor pullback, is triangulated, and has a natural counit invertible on every K-flat complex; exact inverse image preserves K-flat resolutions. The shared SheafOfModules category instances are used throughout."
 },
 "reviewed_lean": {
  "date": "2026-10-11",
  "by": "L",
  "reviewer": "R-ddp1300",
  "group": "K1",
  "result": "pass",
  "note": "g:T⟶S on Scheme.{u}; source/target schemeDerivedCategory S/T on the moduleRings carrier with sibling HasDerivedCategory.{w} binders; L pinned by IsLeftDerivedFunctor ε for E pinned (obj/map eqToHom) to tensorPullbackObj/Map g; CommShift+IsTriangulated; ε invertible on every IsKFlat P (Lg*E ≅ g*P); I pinned to inverseImageModule/Map, exact, carries K-flat resolutions to K-flat resolutions over inverseImageRing (06YC); def = Classical.choose as exists_tensorPullbackAdjunction; no source/Mathlib O_X-module derived pullback (source only étale upperStar.leftDerivedFunctor); recompiled on sheaf-dag c77be01c6 with #check"
 },
 "reviewed_proof": {
  "date": "2026-10-12",
  "by": "L",
  "reviewer": "COMPILER",
  "group": "S1",
  "result": "pass",
  "landing": "20261012T063519-L-3159337",
  "kind": "interface",
  "note": "AUTO: proofs only; landed in a batch after the tools' static checks; compiled with the probe by the group's delivery tool, verified by the global build (compile, axioms, sorry, 60 s per file); not read by a reviewer (stage 3, decision of the human 2026-10-12)"
 }
}
```

### Original snapshot: `dag/nodes/sec-picard-framework/def-pc-module-kflat-complex.json`

SHA-256: `edfb9e007da660d70fd2c3527e1b66f69e77ff756e5fdee99231ac84833b9330`

```json
{
 "id": "def-pc-module-kflat-complex",
 "kind": "definition",
 "title": "K-flat complexes of modules over a commutative ring",
 "status": "split",
 "statement": "Let $R$ be a commutative ring and $K$ a cochain complex of $R$-modules [def-weil-abstract-derived-category]. It is K-flat if for every acyclic complex $F$ of $R$-modules the total tensor complex $\\operatorname{Tot}(F\\otimes_R K)$ [def-pc-tensor-complex-sheaves], specialized to ordinary modules, is acyclic. Equivalently, tensoring with $K$ on either side preserves quasi-isomorphisms of cochain complexes. A K-flat resolution is a quasi-isomorphism $K\\to M$ with $K$ K-flat. This is the ordinary-module specialization of the ringed-site notion [def-pc-kflat-complex].",
 "stmt_deps": [
  "def-weil-abstract-derived-category",
  "def-pc-tensor-complex-sheaves",
  "def-pc-kflat-complex"
 ],
 "source": {
  "document": "literature/stacks-project/more-algebra.tex",
  "place": "Definition 06XZ (definition-K-flat), Section 06XY; the equivalent quasi-isomorphism criterion via mapping cones and signed symmetry"
 },
 "proof": [],
 "proof_deps": [],
 "proof_origin": null,
 "mathlib_match": null,
 "mathlib_searches": [
  {
   "tool": "leanfinder",
   "query": "balanced derived tensor product of an A-module complex and an R-algebra computed by K-flat resolutions with commuting actions",
   "results": "8 hits: HomologicalComplex.HasGoodTensor₁₂, HomologicalComplex.HasTensor, HomologicalComplex.instHasGoodTensor₁₂OfHasGoodTensor₁₂TensorX, HomologicalComplex.instHasGoodTensor₂₃OfHasGoodTensorTensor₂₃X, HomologicalComplex.HasGoodTensor₂₃, HomologicalComplex.tensorObj, HomologicalComplex.instHasTensorOfHasTensorX, HomologicalComplex.ιTensorObj",
   "date": "2026-10-11",
   "verdict": "ingredients only; no exact mixed tensor theorem or ring-specialized K-flat node"
  },
  {
   "tool": "loogle",
   "query": "CategoryTheory.DerivedCategory, CochainComplex",
   "results": "0 hits: ; loogle: unknown identifier 'CategoryTheory.DerivedCategory'",
   "date": "2026-10-11",
   "verdict": "ingredients only; no exact mixed tensor theorem or ring-specialized K-flat node"
  },
  {
   "tool": "grep",
   "query": "KFlat|balanced.*tensor",
   "results": "0 hits: ",
   "date": "2026-10-11",
   "verdict": "ingredients only; no exact mixed tensor theorem or ring-specialized K-flat node"
  },
  {
   "tool": "leansearch",
   "query": "K-flat module complex tensor with every acyclic complex is acyclic",
   "results": "Service unavailable: service unavailable: Internal Server Error",
   "date": "2026-10-11",
   "verdict": "unavailable"
  },
  {
   "tool": "leanfinder",
   "query": "mixed total tensor product complex A modules R modules extension scalars",
   "results": "8 hits: HomologicalComplex.tensorObj, HomologicalComplex.ιTensorObj, HomologicalComplex.HasTensor, HomologicalComplex.tensorHom, HomologicalComplex.HasGoodTensor₁₂, HomologicalComplex.instHasTensorOfHasTensorX, HomologicalComplex.HasGoodTensor₂₃, HomologicalComplex.instHasGoodTensor₂₃OfHasGoodTensorTensor₂₃X",
   "date": "2026-10-11",
   "verdict": "ingredients only; no exact mixed tensor theorem or ring-specialized K-flat node"
  },
  {
   "tool": "grep",
   "query": "mixedTensor|IsKFlat|KFlat|map₂CochainComplex",
   "results": "6 hits: Mathlib/Algebra/Homology/Bifunctor.lean, Mathlib/Algebra/Homology/BifunctorShift.lean, Mathlib/Algebra/Homology/BifunctorShift.lean, Mathlib/Algebra/Homology/BifunctorShift.lean, Mathlib/Algebra/Homology/BifunctorShift.lean, Mathlib/Algebra/Homology/BifunctorShift.lean",
   "date": "2026-10-11",
   "verdict": "ingredients only; no exact mixed tensor theorem or ring-specialized K-flat node"
  },
  {
   "tool": "grep",
   "query": "rg mixedTensor|IsModuleKFlat|exists_balancedDerivedTensorModel in WeilConjectures, lean/Sheaf, dag/lean_names_upstream.json; rg KFlat in WeilConjectures/FromJoel/CategoryTheory/Abelian/Flat/KFlat.lean; rg -l K-flat dag/nodes/def*.json; blueprint_refs.py search K-flat complex of modules over a ring",
   "results": "No exact specialized declaration/node. Existing generic CategoryTheory.MorphismProperty.kFlat and CochainComplex.kFlat_iff_preservesQuasiIso found and reused; existing sheaf-only CochainComplex.IsKFlat cannot take ModuleCat complexes. Existing generic mapBifunctor and ModuleCat.extendScalars found and reused.",
   "date": "2026-10-11",
   "verdict": "Reuse generic source K-flat predicate; introduce mixed coefficient total tensor specialization."
  }
 ],
 "created": {
  "by": "worker",
  "item": "lem-pc-balanced-derived-tensor-model",
  "date": "2026-10-11",
  "group": "E1"
 },
 "blueprint": {
  "is": null,
  "from": {
   "node": "lem-pc-rf-perfect-base-change",
   "place": "choose K-flat module models and form their total tensor over R in the proof of Tag 0DJ8",
   "via": [
    "lem-pc-balanced-derived-tensor-model",
    "lem-pc-derived-tensor-localization-cohomology",
    "lem-pc-affine-derived-base-change-comparison-map",
    "lem-pc-rf-single-complex-affine-base-change",
    "lem-pc-rf-single-complex-qcqs-induction",
    "lem-pc-rf-base-change-single-complex-criterion",
    "lem-pc-rf-base-change-complex",
    "lem-pc-proper-support-perfect-direct-image"
   ]
  },
  "same_as": []
 },
 "lean_audit": {
  "master": {
   "state": "closed",
   "decls": [
    {
     "name": "CategoryTheory.MorphismProperty.kFlat",
     "module": "WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat",
     "lines": [
      34,
      36
     ],
     "kind": "def",
     "sorry": false
    }
   ],
   "missing": [],
   "open": []
  },
  "slopmaster2": {
   "state": "closed",
   "decls": [
    {
     "name": "CategoryTheory.MorphismProperty.kFlat",
     "module": "WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat",
     "lines": [
      34,
      36
     ],
     "kind": "def",
     "sorry": false
    }
   ],
   "missing": [],
   "open": []
  }
 },
 "chapter": "sec-picard-framework",
 "unit": "sk-thm-picard-semicon",
 "lean": {
  "module": "WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat",
  "declaration": "CategoryTheory.MorphismProperty.kFlat",
  "statement": "def kFlat : ObjectProperty C",
  "branch": "slopmaster2",
  "by": "E1",
  "date": "2026-10-11",
  "existing": true,
  "note": "Use (HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)).kFlat. The generic source predicate says tensoring on either side preserves quasi-isomorphisms; over commutative rings this is equivalent to Definition 06XZ by cones and signed symmetry. CochainComplex.kFlat_iff_preservesQuasiIso in WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat exposes this specialization. No private duplicate is defined; a resolution is expressed directly by QuasiIso q and this predicate."
 },
 "reviewed": {
  "date": "2026-10-11",
  "by": "L",
  "reviewer": "R-bdt0940",
  "group": "E1",
  "result": "fix",
  "note": "new definition node of a stage-2 delivery, read against its source by the reviewer"
 },
 "reviewed_lean": {
  "date": "2026-10-11",
  "by": "L",
  "reviewer": "R-bdt0940",
  "group": "E1",
  "result": "fix",
  "note": "Matched clause by clause: R,A,R' CommRing + Algebra R A/R R' (common universe uB, HasDerivedCategory wA/wR); K-flat resolution P->M over A (QuasiIso + source kFlat over ModuleCat A) and F->R'[0] over R; T bifunctor D(A)->D(R)->D(A) with alpha M left-derived of Tot(M (x)_R -) along Q_R, iso on K-flat F; unique e : Q Tot(P(x)_R F) = T(QM)(QE) fixed by both resolution maps; naturality in M; rho : R'->+* End via mulLeft, Commute with a.1_M, A(x)_R R'-module on every H^i with b=1 recovering A. New node def-pc-module-kflat-complex: existing true on slopmaster2 MorphismProperty.kFlat (source states HomotopyCategory.kFlat_iff_preserves_acyclic = 06XZ), no DAG node carries it; def-pc-mixed-total-tensor not in Mathlib/source (grep extendScalars/mixedTensor), map2CochainComplex = mapBifunctor. Fix: mixed-total-tensor statement now cites def-weil-pbc-module-tensor-product and def-weil-module-base-change. Edge: zero rings/complexes, unbounded."
 }
}
```

### Original snapshot: `dag/nodes/sec-picard-framework/lem-pc-affine-derived-pullback-tensor-tilde.json`

SHA-256: `b1ce52669d8042b8bd27cef2c6ba996b81942d62d9f43b0552b641ea7115f81b`

```json
{
 "id": "lem-pc-affine-derived-pullback-tensor-tilde",
 "blueprint": {
  "is": null,
  "from": {
   "node": "lem-pc-projection-formula",
   "place": "proof steps 1 and 2: the affine-local computation of Lf^* and of the derived tensor product (08DW(2), 08DX(2)) and their compatibility with restriction to opens",
   "via": [
    "lem-pc-derived-pullback-tensor-qcoh"
   ]
  },
  "same_as": []
 },
 "kind": "statement",
 "title": "Affine computation of derived pullback and derived tensor product",
 "statement": "Let $f:X\\to Y$ be a morphism of schemes [def-pc-scheme], with derived pullback $Lf^*$ [def-pc-derived-pullback] and derived categories as in [def-pc-derived-category]; for a scheme $Z$ write $K\\otimes^{\\mathbf L}_{\\mathcal O_Z}L$ for the derived tensor product, the total tensor complex [def-pc-tensor-complex-sheaves] of a K-flat resolution of $K$ [def-pc-kflat-complex] with $L$. (1) For opens $U\\subseteq X$, $V\\subseteq Y$ with $f(U)\\subseteq V$ and $E$ in $D(\\mathcal O_Y)$ there is a canonical isomorphism $(Lf^*E)|_U\\cong L(f|_U)^*(E|_V)$ in $D(\\mathcal O_U)$, and for $K,L$ in $D(\\mathcal O_X)$ a canonical isomorphism $(K\\otimes^{\\mathbf L}_{\\mathcal O_X}L)|_U\\cong K|_U\\otimes^{\\mathbf L}_{\\mathcal O_U}L|_U$. (2) If $X=\\operatorname{Spec}(B)$, $Y=\\operatorname{Spec}(A)$ and $f$ is given by a ring map $A\\to B$, then for every complex $M^\\bullet$ of $A$-modules $Lf^*\\widetilde{M^\\bullet}\\cong\\widetilde{M^\\bullet\\otimes_A^{\\mathbf L}B}$ in $D(\\mathcal O_X)$, where $\\widetilde{(-)}$ is the termwise associated sheaf [lem-weil-pbc-spec-module-tilde-sections] and $\\otimes_A^{\\mathbf L}$ the derived tensor product of complexes of modules. (3) If $X=\\operatorname{Spec}(A)$, then for complexes $M^\\bullet,N^\\bullet$ of $A$-modules $\\widetilde{M^\\bullet}\\otimes^{\\mathbf L}_{\\mathcal O_X}\\widetilde{N^\\bullet}\\cong\\widetilde{M^\\bullet\\otimes_A^{\\mathbf L}N^\\bullet}$ in $D(\\mathcal O_X)$.",
 "source": {
  "document": "literature/stacks-project/perfect.tex",
  "place": "Lemma 36.3.8 (Tag 08DW) part (2) and its proof ('Lf^* is compatible with restricting to open subschemes'), Lemma 36.3.9 (Tag 08DX) part (2); both via Lemma 36.3.6 (perfect-lemma-affine-K-flat)"
 },
 "stmt_deps": [
  "def-pc-scheme",
  "def-pc-derived-pullback",
  "def-pc-derived-category",
  "def-pc-tensor-complex-sheaves",
  "def-pc-kflat-complex",
  "lem-pc-affine-qcoh-derived-equivalence",
  "lem-weil-pbc-spec-module-tilde-sections",
  "def-pc-scheme-derived-tensor-structure",
  "def-pc-module-kflat-complex"
 ],
 "proof": [
  {
   "text": "For derived pullback restriction, extract the left-derived tensor-pullback counits from def-pc-derived-pullback. Form the comparison for successive pullbacks using def-pc-module-pullback and its composition isomorphism. On a K-flat representative all counits are invertible, including the second counit because lem-pc-kflat-pullback-preservation preserves K-flatness. Every derived object is isomorphic to a localized K-flat resolution by lem-pc-kflat-resolution, so naturality makes the comparison invertible everywhere. Identify tensor pullback along an open inclusion with exact restriction by uniqueness of left adjoints using Scheme.Modules.nonempty_tensorPullbackAdjunction from def-pc-module-pullback and Mathlib restrictAdjunction and overFunctorEquiv. Exact restriction computes its own derived functor. The equality resLE_comp_ι and the two composition comparisons give the required natural restriction isomorphism. For tensor restriction, apply lem-pc-derived-pullback-tensor-product to the open inclusion to obtain the natural total-complex comparison and its invertibility on K-flat pairs. Apply lem-pc-derived-pullback-tensor-comparison-descent to get the natural comparison of derived bifunctors. Transport both its tensor-before and tensor-after sides through the proved open-pullback/exact-restriction natural isomorphism using curriedTensorPostFunctor and curriedTensorPreFunctor. This proves derivedTensor_openRestriction_iso, including the empty and whole open cases.",
   "uses": [
    "def-pc-derived-pullback",
    "def-pc-module-pullback",
    "lem-pc-kflat-resolution",
    "lem-pc-kflat-pullback-preservation",
    "lem-pc-derived-pullback-tensor-product",
    "lem-pc-derived-pullback-tensor-comparison-descent"
   ],
   "elementary": false,
   "source": {
    "document": "literature/stacks-project/perfect.tex",
    "place": "Tags 08DW and 08DX, restriction steps; Cohomology Tag 079U for the tensor comparison"
   }
  },
  {
   "text": "For affine pullback on K-flat module models, convert the categorical module K-flat predicate to acyclicity of tensor with an acyclic complex using the homotopy-category K-flat criterion. Apply [lem-pc-affine-tilde-kflat]. Extract the tensor-pullback part of the chosen derived pullback specification (without unpacking its unused inverse-image witnesses). The object and morphism equations prove equality of the recorded ordinary functor with tensorPullback. Unpack its counit [def-pc-derived-pullback]; it is invertible on those tilde complexes. Whisker this invertible counit and the natural tilde/base-change comparison [lem-weil-pbc-tilde-pullback-base-change], lifted degreewise to complexes. Compose with quotientCompQhIso and mapHomotopyCategoryFactors to obtain derivedPullback_tilde_kFlat_natIso. Generic proved helpers compose the localization/counit comparison and the degreewise base-change comparison before specialization to affine tilde; this avoids repeated kernel unfolding of the concrete tensor-pullback definitions.",
   "uses": [
    "lem-pc-affine-tilde-kflat",
    "def-pc-derived-pullback",
    "lem-weil-pbc-tilde-pullback-base-change"
   ],
   "elementary": false
  },
  {
   "text": "For the natural affine tensor comparison, termwise tilde of each module K-flat model is K-flat by [lem-pc-affine-tilde-kflat], after the proved homotopy-category acyclicity criterion. Apply [lem-pc-kflat-derived-tensor-comparison] to these first models and arbitrary tilde second models. The statement [lem-pc-affine-tilde-total-tensor] already includes localization by Q; precompose its first variable with the K-flat inclusion, and compose the two natural isomorphisms. This proves derivedTensor_tilde_kFlat_natIso by composition of distinct derived and underived computations.",
   "uses": [
    "lem-pc-affine-tilde-kflat",
    "lem-pc-kflat-derived-tensor-comparison",
    "lem-pc-affine-tilde-total-tensor"
   ],
   "elementary": false
  },
  {
   "text": "For any specified quasi-isomorphism s:P→M, use the functor factorization in [lem-pc-affine-qcoh-derived-equivalence] to show that Q(tilde(s)) is an isomorphism: Q inverts s, and the equivalence and full-subcategory inclusion preserve isomorphisms. Invert this isomorphism, apply derived pullback for the pullback formula or tensor with Q(tilde(N)) for the tensor formula, then compose with the component at P of the corresponding K-flat natural comparison (the tensor comparison is now reduced to the two separate computation statements). Thus the two object formulas hold for every given resolution without choosing another resolution. The final object transport is performed by generic proved map-isomorphism and tensor-isomorphism lemmas; these preserve the comparison statements unchanged.",
   "uses": [
    "lem-pc-affine-qcoh-derived-equivalence"
   ],
   "elementary": false
  }
 ],
 "proof_deps": [
  "def-pc-derived-pullback",
  "def-pc-module-pullback",
  "lem-pc-kflat-resolution",
  "lem-pc-kflat-pullback-preservation",
  "lem-pc-derived-pullback-tensor-product",
  "lem-pc-derived-pullback-tensor-comparison-descent",
  "lem-pc-affine-tilde-kflat",
  "lem-weil-pbc-tilde-pullback-base-change",
  "lem-pc-kflat-derived-tensor-comparison",
  "lem-pc-affine-tilde-total-tensor",
  "lem-pc-affine-qcoh-derived-equivalence"
 ],
 "proof_origin": {
  "by": "document",
  "document": "literature/stacks-project/perfect.tex",
  "place": "Tags 08DV, 08DW(2), 08DX(2); Cohomology Tag 079U. B3 proves both open-restriction comparisons and specializes generic proved comparison and object-transport lemmas to avoid expensive repeated kernel unfolding. The affine quasi-isomorphism transport retains the existing affine derived equivalence route. All six public signatures remain unchanged."
 },
 "mathlib_searches": [
  {
   "tool": "leanfinder",
   "query": "derived pullback along Spec B -> Spec A of the sheaf associated to a complex of A-modules is the sheaf associated to the derived tensor product with B",
   "results": "AlgebraicGeometry.Scheme.Modules.pullback; SheafOfModules.pullback; pullbackPushforwardAdjunction; instIsLeftAdjointPullback (underived only)",
   "date": "2026-10-11",
   "verdict": "no match"
  },
  {
   "tool": "loogle",
   "query": "DerivedCategory, Scheme.Modules.pullback, tensorObj",
   "results": "0 hits; unknown identifier Scheme.Modules.pullback",
   "date": "2026-10-11",
   "verdict": "no match"
  },
  {
   "tool": "grep",
   "query": "derived.*pullback|tensor.*tilde|K-flat in Mathlib/AlgebraicGeometry",
   "results": "0 matches",
   "date": "2026-10-11",
   "verdict": "no match"
  }
 ],
 "mathlib_match": null,
 "status": "split",
 "created": {
  "item": "lem-pc-derived-pullback-tensor-qcoh"
 },
 "chapter": "sec-picard-framework",
 "unit": "sk-thm-picard-f-representable",
 "split_report": {
  "date": "2026-10-11",
  "item": "lem-pc-affine-derived-pullback-tensor-tilde",
  "worker": "stage1",
  "summary": "Split the affine derived pullback and tensor assertions into restriction, affine pullback, and affine tensor steps. The proof uses the existing K-flat resolution and pullback-preservation statements together with the defining derived constructions; no clause-restating node was created.",
  "blueprint": "Realizes lem-pc-projection-formula proof steps 1 and 2: the affine-local computation of Lf^* and derived tensor (08DW(2), 08DX(2)) and compatibility with restriction to opens.",
  "tool_uses": [
   {
    "node": "lem-pc-kflat-resolution",
    "why": "The affine computations require existence of K-flat resolutions, a generic derived-tensor input not supplied by this Picard representability unit."
   },
   {
    "node": "lem-pc-kflat-pullback-preservation",
    "why": "Restriction compatibility uses preservation of K-flat complexes under pullback along open immersions, a generic ringed-space input."
   }
  ]
 },
 "tool_uses": [
  "lem-pc-kflat-resolution",
  "lem-pc-kflat-pullback-preservation",
  "lem-weil-pbc-tilde-pullback-base-change",
  "lem-weil-pbc-affine-tilde-tensor",
  "lem-weil-pbc-spec-module-tilde-sections",
  "lem-pc-kflat-resolution",
  "lem-pc-kflat-pullback-preservation"
 ],
 "reviewed": {
  "date": "2026-10-10",
  "by": "L",
  "reviewer": "R-apt1948",
  "group": "M1",
  "result": "pass",
  "note": "mechanical checks by tools/merge_delivery.py; mathematics reviewed in full by R-apt1948 (reviewer sub-agent of L); spot-checked: Item vs Stacks 08DW(2), 08DX(2) and restriction clause; all cited statements read (kflat-resolution, kflat-pullback-preservation, derived-pullback, tensor-complex, kflat-complex, affine-qcoh-derived-equivalence). Step 1 correct (restrict to V then pull back along f|_U). Small cases: identity ring map, zero complex. FIX more, RETURN less: (1) C1 steps 2,3: K-flatness of tilde(P) over O_{Spec A} (Stacks 08DV, the lemma both Stacks proofs rest on) was used without citation; added statement-only node lem-pc-affine-tilde-kflat (unsplit, grep search recorded) and cited it, with the quasi-iso tilde(P)->tilde(M) via lem-pc-affine-qcoh-derived-equivalence; (2) C1 steps 2,3: tilde commutes with pullback/tensor (01I9, 01I8) asserted without citation; now cite lem-weil-pbc-tilde-pullback-base-change and lem-weil-pbc-affine-tilde-tensor (generic tool uses); (3) statement (E7, citation only, mathematics unchanged): termwise associated sheaf now cites lem-weil-pbc-spec-module-tilde-sections, added to stmt_deps. The Second reading by M1 missed (1) and (2); its claim that created.item was changed is untrue (value is the parent item, which is correct).; 2 file(s) fixed by the reviewer; 1 statement node(s) added by the reviewer (FIX more, RETURN less)"
 },
 "lean_audit": {
  "master": {
   "state": "none",
   "decls": [],
   "missing": []
  },
  "slopmaster2": {
   "state": "none",
   "decls": [],
   "missing": []
  }
 },
 "lean": {
  "module": "Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde",
  "declaration": "AlgebraicGeometry.derivedPullback_openRestriction_iso",
  "declarations": [
   "AlgebraicGeometry.derivedPullback_openRestriction_iso",
   "AlgebraicGeometry.derivedTensor_openRestriction_iso",
   "AlgebraicGeometry.derivedPullback_tilde_iso",
   "AlgebraicGeometry.derivedTensor_tilde_iso",
   "AlgebraicGeometry.derivedPullback_tilde_kFlat_natIso",
   "AlgebraicGeometry.derivedTensor_tilde_kFlat_natIso"
  ],
  "file": "lean/Sheaf/AlgebraicGeometry/AffineDerivedPullbackTensorTilde.lean",
  "statement": "theorem derivedPullback_openRestriction_iso {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (hUV : U ≤ f ⁻¹ᵁ V) [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))] [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))] : Nonempty (derivedPullback f ⋙ (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙ Equivalence.functor (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) (Scheme.Modules.overEquiv U)).mapDerivedCategory ≅ (SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) V ⋙ Equivalence.functor (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V)) (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) (Scheme.Modules.overEquiv V)).mapDerivedCategory ⋙ derivedPullback (f.resLE V U hUV))",
  "branch": "sheaf-dag",
  "by": "F1",
  "date": "2026-10-11",
  "existing": false,
  "note": "The six statements together render all three clauses. The two open-restriction comparisons and the two affine comparisons on K-flat models are natural isomorphisms. The affine object formulas apply to every K-flat resolution P → M, whose scalar-extension or total-tensor complex is precisely the module derived-tensor representative; no boundedness or flatness assumption is imposed."
 },
 "reviewed_lean": {
  "date": "2026-10-11",
  "by": "L",
  "reviewer": "R-apt",
  "group": "F1",
  "result": "pass",
  "note": "clause (1): Lf* ⋙ R_U ≅ R_V ⋙ L(f.resLE V U hUV)* with R = overFunctor ⋙ overEquiv.functor, mapDerivedCategory; (K⊗L)|U ≅ K|U⊗L|U as curried natIso via global schemeDerivedTensorMonoidal; (2) Spec.map φ, Lf* Q(tilde M) ≅ Q(tilde (extendScalars φ P)) for any K-flat qis P→M (recorded MorphismProperty.kFlat), plus natIso on ιKFlat; (3) Q tilde M ⊗ Q tilde N ≅ Q tilde (mapBifunctor P N), natIso via map₂CochainComplex; tilde form as landed 5adffa6dd/qcoh-equivalence; no let/choose/local notation; stmt_deps gained 2 landed used nodes; check_dag unchanged"
 },
 "reviewed_proof": {
  "date": "2026-10-13",
  "by": "L",
  "reviewer": "X-397b1",
  "group": "B3",
  "result": "pass",
  "landing": "20261013T113336-L-3181143",
  "kind": "proof",
  "note": "independent Codex review: Matched the six Lean statements and proofs against the node, dependency declarations, source lemmas, baseline signatures, report, axiom probe, and twelve direct-importer compiles."
 }
}
```

### Original snapshot: `dag/nodes/sec-picard-framework/lem-pc-affine-model-coherent-object-comparisons.json`

SHA-256: `b35ed2b2dddee5372d55d96c57d8b2fb5243a7c339765e011568ee60ef3b58b6`

```json
{
 "id": "lem-pc-affine-model-coherent-object-comparisons",
 "kind": "statement",
 "title": "Coherent affine object comparisons and one-arrow natural isomorphisms",
 "statement": "Under exactly the preorder diagram, cocone, affine scheme, acyclic-tensor K-flat model, coordinate transition, derived equivalence and localization hypotheses of lem-pc-affine-model-comparison-of-bottom-models [def-pc-scheme, def-pc-derived-category, def-pc-derived-pullback, def-pc-module-kflat-complex], there is a nonempty AffineModelCoherentObjects structure. Its fields are object isomorphisms αE(j),αK(j),βE,βK from the localized tilde of the bottom models extended to each stage and the cocone ring, to derived pullbacks of P,Q; natural comparisons θ(j,k),θlim(j) between scalar extension followed by localized tilde and localized tilde followed by geometric derived pullback; and iso-level triangles. Each natural comparison is on the full induced category on the two labelled extended models, retaining all morphisms even for coincident objects. The triangle says localized scalar reassociation [def-pc-complex-scalar-extension-hom], θ, pullback of α, and inverse perfectHomComparison [lem-pc-perfect-hom-transport] compose to the target object isomorphism, for both E and K and for finite and cocone arrows. No equation on conjugated arbitrary chain maps is asserted. The structure and its field types are explicit definitions, not chosen data. No directedness, colimit, boundedness or flatness of ring maps is assumed. Identity arrows, zero complexes, coincident models, zero rings and empty spectra are included.",
 "source": {
  "document": "https://stacks.math.columbia.edu/tag/08DW",
  "place": "Tag 09RE affine calculation, Tag 08DW(2), Tags 06Y1 and 0D5S; core proof steps 2–3 after bottom-model identification"
 },
 "stmt_deps": [
  "def-pc-scheme",
  "def-pc-derived-category",
  "def-pc-derived-pullback",
  "def-pc-module-kflat-complex",
  "def-pc-complex-scalar-extension-hom",
  "lem-pc-perfect-hom-transport"
 ],
 "proof": [
  {
   "text": "Use natural affine derived pullback on the two K-flat extended models. Identify the scalar-extended tilde functor with pullback of the localized tilde functor, transport through hd at source and target, and use the coordinate transition equation. This defines each natural θ on the full two-label induced category.",
   "uses": [
    "lem-pc-affine-derived-pullback-tensor-tilde",
    "lem-pc-kflat-extension-of-scalars",
    "lem-pc-ringed-spaces-derived-pullback-composition"
   ],
   "elementary": false
  },
  {
   "text": "At the bottom-to-stage and bottom-to-limit arrows, evaluate the affine comparison at E,K, pull back aE,aK and compose with inverse perfectHomComparison to construct αE(j),αK(j),βE,βK. Identity scalar extension uses F.map_id. For bottom→j→k and bottom→j→limit, use F.map_comp or C.w and the counit characterization and associativity of derived composition. On K-flat representatives the reassociation is the explicit affineModelScalarAssocIso. Transport through hd,hdlim and aE,aK to obtain the four iso-level triangles, and package the constructed fields into AffineModelCoherentObjects.",
   "uses": [
    "lem-pc-affine-derived-pullback-tensor-tilde",
    "lem-pc-ringed-spaces-derived-pullback-composition",
    "lem-pc-perfect-hom-transport",
    "def-pc-complex-scalar-extension-hom"
   ],
   "elementary": false
  }
 ],
 "proof_origin": {
  "by": "agent",
  "document": "https://stacks.math.columbia.edu/tag/08DW",
  "place": "Tag 09RE affine model calculation, Tag 06Y1 scalar-extension preservation, and the counit-pinned composition comparisons of Tag 0D5S. The data types and coherence predicate are named explicit definitions to avoid duplicating anonymous dependent functors."
 },
 "mathlib_searches": [
  {
   "tool": "leansearch",
   "query": "Natural affine derived pullback comparison compatible with composition on K-flat complexes",
   "results": "Service unavailable: Internal Server Error",
   "date": "2026-10-14",
   "verdict": "unavailable"
  },
  {
   "tool": "leanfinder",
   "query": "Natural derived pullback comparison for K-flat module complexes along compatible affine scheme isomorphisms",
   "results": "Scheme.Modules.pullbackComp, pullbackSpecIso_hom_base and generic sheaf pullback results.",
   "date": "2026-10-14",
   "verdict": "No localized-coordinate model comparison or diagram propagation theorem."
  },
  {
   "tool": "loogle",
   "query": "ModuleCat.extendScalarsComp",
   "results": "extendScalarsComp and extendScalars_assoc provide associativity; no geometric model transport theorem.",
   "date": "2026-10-14",
   "verdict": "Use for the remaining coherence calculation."
  },
  {
   "tool": "grep",
   "query": "affineModelComparisonData|derivedPullback_tilde_kFlat_natIso|kFlat.*extendScalars|extendScalars.*kFlat",
   "results": "AffineDerivedPullbackTensorTilde has natural affine formulas; KFlatModuleBaseChange has the acyclic-tensor preservation criterion; no single-square comparison or propagation from bottom models.",
   "date": "2026-10-14",
   "verdict": "Use the existing affine and K-flat APIs and isolate only propagation."
  }
 ],
 "mathlib_match": null,
 "status": "split",
 "created": {
  "by": "worker",
  "item": "Sheaf.AlgebraicGeometry.AffineModelComparisonOfBottomModels",
  "date": "2026-10-14",
  "group": "P4"
 },
 "blueprint": {
  "is": null,
  "from": {
   "node": null,
   "place": "Object and natural-comparison part of bottom-stage affine-model propagation; finite and cocone arrows are stated directly.",
   "via": [
    "lem-pc-affine-model-comparison-of-bottom-models",
    "lem-pc-affine-base-change-model-isos-core",
    "lem-pc-affine-base-change-model-isos-of-scheme-comparisons"
   ]
  },
  "same_as": []
 },
 "chapter": "sec-picard-framework",
 "unit": "sk-thm-picard-semicon",
 "lean": {
  "existing": false,
  "module": "Sheaf.AlgebraicGeometry.AffineModelCoherentObjectComparisons",
  "file": "lean/Sheaf/AlgebraicGeometry/AffineModelCoherentObjectComparisons.lean",
  "declaration": "AlgebraicGeometry.exists_affineModelCoherentObjectComparisons",
  "declarations": [
   "AlgebraicGeometry.affineModelTildeComplex",
   "AlgebraicGeometry.affineModelLocalizedTilde",
   "AlgebraicGeometry.affineModelLocalizedTilde_map",
   "AlgebraicGeometry.affineModelScalarPair",
   "AlgebraicGeometry.affineModelScalarAssocIso",
   "AlgebraicGeometry.affineModelScalarAssocIso_hom",
   "AlgebraicGeometry.affineModelScalarAssocIso_inv",
   "AlgebraicGeometry.affineModelStageArrow",
   "AlgebraicGeometry.affineModelLimitArrow",
   "AlgebraicGeometry.affineModel_scalarConjugation_nat",
   "AlgebraicGeometry.AffineModelStageObjects",
   "AlgebraicGeometry.AffineModelLimitObject",
   "AlgebraicGeometry.AffineModelStageArrowComparisons",
   "AlgebraicGeometry.AffineModelLimitArrowComparisons",
   "AlgebraicGeometry.affineModelStageObjectCoherence",
   "AlgebraicGeometry.affineModelLimitObjectCoherence",
   "AlgebraicGeometry.AffineModelCoherentObjects",
   "AlgebraicGeometry.exists_affineModelCoherentObjectComparisons"
  ],
  "statement": "theorem exists_affineModelCoherentObjectComparisons {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (i : I) (Y : Scheme.{u}) [IsAffine Y] (s : Y ⟶ Spec (R.obj i)) [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] (P Q : schemeDerivedCategory Y) (F : Set.Ici i ⥤ CommRingCat.{u}) (C : Cocone F) (E K : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ) (hE : ∀ L : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ, L.Acyclic → (CochainComplex.mapBifunctor L E (MonoidalCategory.curriedTensor (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)))).Acyclic) (hK : ∀ L : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ, L.Acyclic → (CochainComplex.mapBifunctor L K (MonoidalCategory.curriedTensor (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)))).Acyclic) (σ : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i), Spec (F.obj j.val) ≅ pullback s (Spec.map (R.map (homOfLE j.val.property)))) (τ : Spec C.pt ≅ pullback s (Spec.map (c.ι.app i))) (htrans : (∀ (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k), (σ k).hom ≫ baseChangeMap s (T := Over.mk (Spec.map (R.map (homOfLE j.val.property)))) (T' := Over.mk (Spec.map (R.map (homOfLE k.val.property)))) (Over.homMk (Spec.map (R.map (homOfLE hjk))) (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)) = Spec.map (F.map (homOfLE hjk)) ≫ (σ j).hom) ∧ (∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i), τ.hom ≫ baseChangeMap s (T := Over.mk (Spec.map (R.map (homOfLE j.val.property)))) (T' := Over.mk (Spec.map (c.ι.app i))) (Over.homMk (Spec.map (c.ι.app j.val)) (by dsimp; rw [← Spec.map_comp, c.w (homOfLE j.val.property)])) = Spec.map (C.ι.app j.val) ≫ (σ j).hom)) (d : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i), schemeDerivedCategory (Spec (F.obj j.val)) ≌ schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE j.val.property))))) (dlim : schemeDerivedCategory (Spec (C.pt)) ≌ schemeDerivedCategory (pullback s (Spec.map (c.ι.app i)))) (hd : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i), DerivedCategory.Q ⋙ (d j).functor ≅ (@Functor.mapHomologicalComplex ℤ (SheafOfModules.{u} (moduleRings (Spec (F.obj j.val)).toRingedSpace)) (SheafOfModules.{u} (moduleRings (pullback s (Spec.map (R.map (homOfLE j.val.property)))).toRingedSpace)) _ _ _ _ (SheafOfModules.pushforward (σ j).hom.toRingCatSheafHom) ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q) (hdlim : DerivedCategory.Q ⋙ dlim.functor ≅ (@Functor.mapHomologicalComplex ℤ (SheafOfModules.{u} (moduleRings (Spec C.pt).toRingedSpace)) (SheafOfModules.{u} (moduleRings (pullback s (Spec.map (c.ι.app i))).toRingedSpace)) _ _ _ _ (SheafOfModules.pushforward τ.hom.toRingCatSheafHom) ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q) (aE : (d ⟨⟨i, le_rfl⟩, le_rfl⟩).functor.obj (DerivedCategory.Q.obj ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) (SheafOfModules.{u} (moduleRings (Spec (F.obj ⟨i, le_rfl⟩)).toRingedSpace)) _ _ _ _ (@id (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩) ⥤ SheafOfModules.{u} (moduleRings (Spec (F.obj ⟨i, le_rfl⟩)).toRingedSpace)) (tilde.functor (F.obj ⟨i, le_rfl⟩))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj E)) ≅ (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE (le_refl i)))))).obj P) (aK : (d ⟨⟨i, le_rfl⟩, le_rfl⟩).functor.obj (DerivedCategory.Q.obj ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) (SheafOfModules.{u} (moduleRings (Spec (F.obj ⟨i, le_rfl⟩)).toRingedSpace)) _ _ _ _ (@id (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩) ⥤ SheafOfModules.{u} (moduleRings (Spec (F.obj ⟨i, le_rfl⟩)).toRingedSpace)) (tilde.functor (F.obj ⟨i, le_rfl⟩))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj K)) ≅ (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE (le_refl i)))))).obj Q) : Nonempty (AffineModelCoherentObjects R c i Y s P Q F C E K d dlim)",
  "branch": "sheaf-dag",
  "by": "P4",
  "date": "2026-10-14"
 },
 "proof_deps": [
  "def-pc-complex-scalar-extension-hom",
  "lem-pc-affine-derived-pullback-tensor-tilde",
  "lem-pc-kflat-extension-of-scalars",
  "lem-pc-perfect-hom-transport",
  "lem-pc-ringed-spaces-derived-pullback-composition"
 ],
 "reviewed": {
  "date": "2026-10-14",
  "by": "L",
  "reviewer": "COMPILER",
  "group": "P4",
  "result": "pass",
  "landing": "20261014T045611-L-1573878",
  "kind": "interface",
  "note": "new node of a stage-3 delivery, read against its source by the reviewer"
 },
 "reviewed_proof": {
  "date": "2026-10-14",
  "by": "L",
  "reviewer": "COMPILER",
  "group": "P4",
  "result": "pass",
  "landing": "20261014T045611-L-1573878",
  "kind": "interface",
  "note": "AUTO: proofs only; landed in a batch after the tools' static checks; compiled with the probe by the group's delivery tool, verified by the global build (compile, axioms, sorry, 60 s per file); not read by a reviewer (stage 3, decision of the human 2026-10-12)"
 }
}
```

### Original snapshot: `dag/nodes/sec-picard-framework/lem-pc-affine-model-comparison-data-from-hom-equations.json`

SHA-256: `b6720c46eb986191a39590a705d5b01d0c86826c08b75522752efe7cbce76347`

```json
{
 "id": "lem-pc-affine-model-comparison-data-from-hom-equations",
 "kind": "statement",
 "title": "Constructor interface for explicit affine comparison data",
 "statement": "For the preorder, diagram, cocone, affine scheme and chosen derived categories of def-pc-affine-model-comparison-data, fix d,dlim and four comparison families αE,αK,βE,βK with the canonical object types of lem-pc-affine-model-coherent-object-comparisons. If the localized tilde maps satisfy the finite and cocone conjugation equations with scalarExtensionHom [def-pc-complex-scalar-extension-hom] and perfectStageMap/perfectLimitMap [lem-pc-perfect-hom-transport], then affineModelComparisonData holds with those supplied witnesses. This is only the constructor interface of the explicit comparison predicate: it assumes the Hom equations, does not assert their validity, and has no K-flatness, coordinates, bottom models or natural-comparison hypothesis.",
 "source": {
  "document": "https://stacks.math.columbia.edu/tag/09RE",
  "place": "The explicit formula of def-pc-affine-model-comparison-data and the canonical termwise tilde definition; definitional constructor step."
 },
 "stmt_deps": [
  "def-pc-affine-model-comparison-data",
  "lem-pc-affine-model-coherent-object-comparisons",
  "def-pc-complex-scalar-extension-hom",
  "lem-pc-perfect-hom-transport"
 ],
 "proof": [
  {
   "text": "Expand affineModelComparisonData and use the supplied d,dlim,αE,αK,βE,βK as the six witnesses. The explicit map equation for affineModelLocalizedTilde and the termwise tilde definition identify the two remaining goals with hstage,hlim. Proof irrelevance identifies generated preorder and HasPullback proof constants with the direct instances. All scalarExtensionHom and geometric Hom-transport terms are unchanged. No geometric argument or witness choice occurs.",
   "uses": [
    "def-pc-affine-model-comparison-data",
    "lem-pc-affine-model-coherent-object-comparisons",
    "def-pc-complex-scalar-extension-hom",
    "lem-pc-perfect-hom-transport"
   ],
   "elementary": true
  }
 ],
 "proof_origin": {
  "by": "agent",
  "document": "https://stacks.math.columbia.edu/tag/09RE",
  "place": "Definitional introduction of the explicitly stated affine comparison-data formula; source representations are given by real named functor definitions."
 },
 "mathlib_searches": [
  {
   "tool": "leansearch",
   "query": "Natural affine derived pullback comparison compatible with composition on K-flat complexes",
   "results": "Service unavailable: Internal Server Error",
   "date": "2026-10-14",
   "verdict": "unavailable"
  },
  {
   "tool": "leanfinder",
   "query": "Natural derived pullback comparison for K-flat module complexes along compatible affine scheme isomorphisms",
   "results": "Scheme.Modules.pullbackComp, pullbackSpecIso_hom_base and generic sheaf pullback results.",
   "date": "2026-10-14",
   "verdict": "No localized-coordinate model comparison or diagram propagation theorem."
  },
  {
   "tool": "loogle",
   "query": "ModuleCat.extendScalarsComp",
   "results": "extendScalarsComp and extendScalars_assoc provide associativity; no geometric model transport theorem.",
   "date": "2026-10-14",
   "verdict": "Use for the remaining coherence calculation."
  },
  {
   "tool": "grep",
   "query": "affineModelComparisonData|derivedPullback_tilde_kFlat_natIso|kFlat.*extendScalars|extendScalars.*kFlat",
   "results": "AffineDerivedPullbackTensorTilde has natural affine formulas; KFlatModuleBaseChange has the acyclic-tensor preservation criterion; no single-square comparison or propagation from bottom models.",
   "date": "2026-10-14",
   "verdict": "Use the existing affine and K-flat APIs and isolate only propagation."
  }
 ],
 "mathlib_match": null,
 "status": "split",
 "created": {
  "by": "worker",
  "item": "Sheaf.AlgebraicGeometry.AffineModelComparisonOfBottomModels",
  "date": "2026-10-14",
  "group": "P4"
 },
 "blueprint": {
  "is": null,
  "from": {
   "node": null,
   "place": "Definition-interface glue after proving the arbitrary-chain-map equations",
   "via": [
    "lem-pc-affine-model-comparison-of-bottom-models"
   ]
  },
  "same_as": []
 },
 "chapter": "sec-picard-framework",
 "unit": "sk-thm-picard-semicon",
 "lean": {
  "existing": false,
  "module": "Sheaf.AlgebraicGeometry.AffineModelComparisonDataFromHomEquations",
  "file": "lean/Sheaf/AlgebraicGeometry/AffineModelComparisonDataFromHomEquations.lean",
  "declaration": "AlgebraicGeometry.affineModelComparisonData_of_hom_equations",
  "declarations": [
   "AlgebraicGeometry.affineModelComparisonData_of_hom_equations"
  ],
  "statement": "theorem affineModelComparisonData_of_hom_equations {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (i : I) (Y : Scheme.{u}) [IsAffine Y] (s : Y ⟶ Spec (R.obj i)) [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] (P Q : schemeDerivedCategory Y) (F : Set.Ici i ⥤ CommRingCat.{u}) (C : Cocone F) (E K : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ) (d : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i), schemeDerivedCategory (Spec (F.obj j.val)) ≌ schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE j.val.property))))) (dlim : schemeDerivedCategory (Spec (C.pt)) ≌ schemeDerivedCategory (pullback s (Spec.map (c.ι.app i)))) (αE : AffineModelStageObjects R i Y s P F E d) (αK : AffineModelStageObjects R i Y s Q F K d) (βE : AffineModelLimitObject R c i Y s P F C E dlim) (βK : AffineModelLimitObject R c i Y s Q F C K dlim) (hstage : ∀ (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k) (a : ((Functor.mapHomologicalComplex (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ))).obj E ⟶ ((Functor.mapHomologicalComplex (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ))).obj K), (αE k).inv ≫ (affineModelLocalizedTilde (F.obj k.val) _ (d k)).map (CochainComplex.scalarExtensionHom (F.map (homOfLE j.property)).hom (F.map (homOfLE hjk)).hom (F.map (homOfLE k.property)).hom (congrArg CommRingCat.Hom.hom (F.map_comp (homOfLE j.property) (homOfLE hjk))) E K a) ≫ (αK k).hom = perfectStageMap R s j.val.property hjk ((αE j).inv ≫ (affineModelLocalizedTilde (F.obj j.val) _ (d j)).map a ≫ (αK j).hom)) (hlim : ∀ (j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (a : ((Functor.mapHomologicalComplex (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ))).obj E ⟶ ((Functor.mapHomologicalComplex (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ))).obj K), βE.inv ≫ (affineModelLocalizedTilde C.pt _ dlim).map (CochainComplex.scalarExtensionHom (F.map (homOfLE j.property)).hom (C.ι.app j.val).hom (C.ι.app ⟨i, le_rfl⟩).hom (congrArg CommRingCat.Hom.hom (C.w (homOfLE j.property)).symm) E K a) ≫ βK.hom = perfectLimitMap R c s j.val.property ((αE j).inv ≫ (affineModelLocalizedTilde (F.obj j.val) _ (d j)).map a ≫ (αK j).hom)) : affineModelComparisonData R c i Y s P Q F C E K",
  "branch": "sheaf-dag",
  "by": "P4",
  "date": "2026-10-14"
 },
 "proof_deps": [
  "def-pc-affine-model-comparison-data",
  "lem-pc-affine-model-coherent-object-comparisons",
  "def-pc-complex-scalar-extension-hom",
  "lem-pc-perfect-hom-transport"
 ],
 "reviewed": {
  "date": "2026-10-14",
  "by": "L",
  "reviewer": "COMPILER",
  "group": "P4",
  "result": "pass",
  "landing": "20261014T045611-L-1573878",
  "kind": "interface",
  "note": "new node of a stage-3 delivery, read against its source by the reviewer"
 },
 "reviewed_proof": {
  "date": "2026-10-14",
  "by": "L",
  "reviewer": "AUTO",
  "group": "U2",
  "result": "pass",
  "landing": "20261014T053242-L-2011157",
  "kind": "proof",
  "note": "AUTO: proofs only; landed in a batch after the tools' static checks; compiled with the probe by the group's delivery tool, verified by the global build (compile, axioms, sorry, 60 s per file); not read by a reviewer (stage 3, decision of the human 2026-10-12)",
  "sorry_before": [
   "AlgebraicGeometry.affineModelComparisonData_of_hom_equations"
  ],
  "sorry_after": []
 }
}
```

### Original snapshot: `dag/nodes/sec-picard-framework/lem-pc-affine-model-comparison-of-bottom-models.json`

SHA-256: `05e8fbe9ee71935ffcb2c6e6bd4dca926e9d636f95a7858ac23a1e58067b5c31`

```json
{
 "id": "lem-pc-affine-model-comparison-of-bottom-models",
 "kind": "statement",
 "title": "Propagation of two bottom-stage affine models",
 "statement": "Let I be a preorder, R:I→CommRing a diagram, c its cocone, i∈I, Y an affine scheme, s:Y→Spec R(i), and P,Q∈D(Y), with scheme derived categories [def-pc-scheme, def-pc-derived-category]. Let F be any ring diagram on the upper tail Ici i, C any cocone, and E,K module complexes over F(i) satisfying the acyclic-tensor K-flat criterion [def-pc-module-kflat-complex]. Specify stage scheme isomorphisms σ(j):Spec F(j)≅Y×Spec R(j), τ:Spec C.pt≅Y×Spec c.pt, commuting with every finite-stage and limit transition. Specify derived equivalences d(j),dlim with natural localization comparisons identifying them with termwise pushforward along σ(j).hom,τ.hom. Given isomorphisms aE:d(i)(Q(tilde E))≅Lp(i)*P and aK:d(i)(Q(tilde K))≅Lp(i)*Q at the bottom stage, affineModelComparisonData(R,c,i,Y,s,P,Q,F,C,E,K) [def-pc-affine-model-comparison-data] holds. No Γ(Y)-models, initial ring map from Γ(Y), or first-projection equations are assumed. The only geometric inputs beyond the isomorphisms are transition equations and the two bottom object comparisons. No directedness, colimit property, flatness or boundedness is required.",
 "source": {
  "document": "https://stacks.math.columbia.edu/tag/08DW",
  "place": "Tag 09RE affine calculation, Tag 08DW(2), Tags 06Y1 and 0D5S; core proof steps 2–3 after bottom-model identification"
 },
 "stmt_deps": [
  "def-pc-scheme",
  "def-pc-derived-category",
  "def-pc-derived-pullback",
  "def-pc-module-kflat-complex",
  "def-pc-affine-model-comparison-data",
  "def-pc-complex-scalar-extension-hom",
  "lem-pc-perfect-hom-transport"
 ],
 "proof": [
  {
   "text": "Obtain coherent object comparisons and natural comparisons with object triangles. These are real types under Nonempty, never definitions choosing a witness from unproved existence.",
   "uses": [
    "lem-pc-affine-model-coherent-object-comparisons"
   ],
   "elementary": false
  },
  {
   "text": "Apply the finite-stage and cocone Hom-equation interfaces to the same supplied comparison objects. The generic scalar reassociation and naturality cancellation calculation is proved in the coherent-object module; specialization and representation glue remain these two named obligations.",
   "uses": [
    "lem-pc-affine-model-stage-hom-equation-of-coherent-objects",
    "lem-pc-affine-model-limit-hom-equation-of-coherent-objects"
   ],
   "elementary": false
  },
  {
   "text": "Apply the constructor interface to d,dlim, the four comparison objects and the two proved or supplied Hom-equation families. This packages exactly the original explicit affineModelComparisonData predicate.",
   "uses": [
    "lem-pc-affine-model-comparison-data-from-hom-equations"
   ],
   "elementary": true
  }
 ],
 "proof_deps": [
  "lem-pc-affine-model-coherent-object-comparisons",
  "lem-pc-affine-model-stage-hom-equation-of-coherent-objects",
  "lem-pc-affine-model-limit-hom-equation-of-coherent-objects",
  "lem-pc-affine-model-comparison-data-from-hom-equations"
 ],
 "proof_origin": {
  "by": "agent",
  "document": "https://stacks.math.columbia.edu/tag/08DW",
  "place": "Direct finite and cocone object triangles; generic scalar/naturality calculation is proved, with its two concrete specializations and the definition constructor isolated as interfaces."
 },
 "mathlib_searches": [
  {
   "tool": "leansearch",
   "query": "Natural affine derived pullback comparison compatible with composition on K-flat complexes",
   "results": "Service unavailable: Internal Server Error",
   "date": "2026-10-14",
   "verdict": "unavailable"
  },
  {
   "tool": "leanfinder",
   "query": "Natural derived pullback comparison for K-flat module complexes along compatible affine scheme isomorphisms",
   "results": "Scheme.Modules.pullbackComp, pullbackSpecIso_hom_base and generic sheaf pullback results.",
   "date": "2026-10-14",
   "verdict": "No localized-coordinate model comparison or diagram propagation theorem."
  },
  {
   "tool": "loogle",
   "query": "ModuleCat.extendScalarsComp",
   "results": "extendScalarsComp and extendScalars_assoc provide associativity; no geometric model transport theorem.",
   "date": "2026-10-14",
   "verdict": "Use for the remaining coherence calculation."
  },
  {
   "tool": "grep",
   "query": "affineModelComparisonData|derivedPullback_tilde_kFlat_natIso|kFlat.*extendScalars|extendScalars.*kFlat",
   "results": "AffineDerivedPullbackTensorTilde has natural affine formulas; KFlatModuleBaseChange has the acyclic-tensor preservation criterion; no single-square comparison or propagation from bottom models.",
   "date": "2026-10-14",
   "verdict": "Use the existing affine and K-flat APIs and isolate only propagation."
  }
 ],
 "mathlib_match": null,
 "status": "split",
 "created": {
  "by": "worker",
  "item": "Sheaf.AlgebraicGeometry.AffineBaseChangeModelIsosOfSchemeComparisons",
  "date": "2026-10-14",
  "group": "U2"
 },
 "blueprint": {
  "is": null,
  "from": {
   "node": null,
   "place": "lem-pc-affine-base-change-model-isos-core, Tag 09RE affine calculation, Tag 08DW(2), Tags 06Y1 and 0D5S; core proof steps 2–3 after bottom-model identification",
   "via": [
    "lem-pc-affine-base-change-model-isos-core",
    "lem-pc-affine-base-change-model-isos-of-scheme-comparisons"
   ]
  },
  "same_as": []
 },
 "chapter": "sec-picard-framework",
 "unit": "sk-thm-picard-semicon",
 "lean": {
  "existing": false,
  "module": "Sheaf.AlgebraicGeometry.AffineModelComparisonOfBottomModels",
  "file": "lean/Sheaf/AlgebraicGeometry/AffineModelComparisonOfBottomModels.lean",
  "declaration": "AlgebraicGeometry.affineModelComparisonData_of_bottom_models",
  "statement": "theorem affineModelComparisonData_of_bottom_models {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (i : I) (Y : Scheme.{u}) [IsAffine Y] (s : Y ⟶ Spec (R.obj i)) [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] (P Q : schemeDerivedCategory Y) (F : Set.Ici i ⥤ CommRingCat.{u}) (C : Cocone F) (E K : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ) (hE : ∀ L : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ, L.Acyclic → (CochainComplex.mapBifunctor L E (MonoidalCategory.curriedTensor (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)))).Acyclic) (hK : ∀ L : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ, L.Acyclic → (CochainComplex.mapBifunctor L K (MonoidalCategory.curriedTensor (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)))).Acyclic) (σ : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i), Spec (F.obj j.val) ≅ pullback s (Spec.map (R.map (homOfLE j.val.property)))) (τ : Spec C.pt ≅ pullback s (Spec.map (c.ι.app i))) (htrans : (∀ (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k), (σ k).hom ≫ baseChangeMap s (T := Over.mk (Spec.map (R.map (homOfLE j.val.property)))) (T' := Over.mk (Spec.map (R.map (homOfLE k.val.property)))) (Over.homMk (Spec.map (R.map (homOfLE hjk))) (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)) = Spec.map (F.map (homOfLE hjk)) ≫ (σ j).hom) ∧ (∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i), τ.hom ≫ baseChangeMap s (T := Over.mk (Spec.map (R.map (homOfLE j.val.property)))) (T' := Over.mk (Spec.map (c.ι.app i))) (Over.homMk (Spec.map (c.ι.app j.val)) (by dsimp; rw [← Spec.map_comp, c.w (homOfLE j.val.property)])) = Spec.map (C.ι.app j.val) ≫ (σ j).hom)) (d : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i), schemeDerivedCategory (Spec (F.obj j.val)) ≌ schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE j.val.property))))) (dlim : schemeDerivedCategory (Spec (C.pt)) ≌ schemeDerivedCategory (pullback s (Spec.map (c.ι.app i)))) (hd : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i), DerivedCategory.Q ⋙ (d j).functor ≅ (@Functor.mapHomologicalComplex ℤ (SheafOfModules.{u} (moduleRings (Spec (F.obj j.val)).toRingedSpace)) (SheafOfModules.{u} (moduleRings (pullback s (Spec.map (R.map (homOfLE j.val.property)))).toRingedSpace)) _ _ _ _ (SheafOfModules.pushforward (σ j).hom.toRingCatSheafHom) ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q) (hdlim : DerivedCategory.Q ⋙ dlim.functor ≅ (@Functor.mapHomologicalComplex ℤ (SheafOfModules.{u} (moduleRings (Spec C.pt).toRingedSpace)) (SheafOfModules.{u} (moduleRings (pullback s (Spec.map (c.ι.app i))).toRingedSpace)) _ _ _ _ (SheafOfModules.pushforward τ.hom.toRingCatSheafHom) ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q) (aE : (d ⟨⟨i, le_rfl⟩, le_rfl⟩).functor.obj (DerivedCategory.Q.obj ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) (SheafOfModules.{u} (moduleRings (Spec (F.obj ⟨i, le_rfl⟩)).toRingedSpace)) _ _ _ _ (@id (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩) ⥤ SheafOfModules.{u} (moduleRings (Spec (F.obj ⟨i, le_rfl⟩)).toRingedSpace)) (tilde.functor (F.obj ⟨i, le_rfl⟩))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj E)) ≅ (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE (le_refl i)))))).obj P) (aK : (d ⟨⟨i, le_rfl⟩, le_rfl⟩).functor.obj (DerivedCategory.Q.obj ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) (SheafOfModules.{u} (moduleRings (Spec (F.obj ⟨i, le_rfl⟩)).toRingedSpace)) _ _ _ _ (@id (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩) ⥤ SheafOfModules.{u} (moduleRings (Spec (F.obj ⟨i, le_rfl⟩)).toRingedSpace)) (tilde.functor (F.obj ⟨i, le_rfl⟩))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj K)) ≅ (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE (le_refl i)))))).obj Q) : affineModelComparisonData R c i Y s P Q F C E K",
  "branch": "sheaf-dag",
  "by": "U2",
  "date": "2026-10-14",
  "declarations": [
   "AlgebraicGeometry.affineModelComparisonData_of_bottom_models"
  ]
 },
 "reviewed": {
  "date": "2026-10-14",
  "by": "L",
  "reviewer": "COMPILER",
  "group": "U2",
  "result": "pass",
  "landing": "20261014T010854-L-3168155",
  "kind": "interface",
  "note": "new node of a stage-3 delivery, read against its source by the reviewer"
 },
 "reviewed_proof": {
  "date": "2026-10-14",
  "by": "L",
  "reviewer": "COMPILER",
  "group": "P4",
  "result": "pass",
  "landing": "20261014T045611-L-1573878",
  "kind": "interface",
  "note": "AUTO: proofs only; landed in a batch after the tools' static checks; compiled with the probe by the group's delivery tool, verified by the global build (compile, axioms, sorry, 60 s per file); not read by a reviewer (stage 3, decision of the human 2026-10-12)"
 }
}
```

### Original snapshot: `dag/nodes/sec-picard-framework/lem-pc-affine-model-limit-hom-equation-of-coherent-objects.json`

SHA-256: `2ff5080909b9ce0d69b9455edb8389e2d2e79e30227461ab0a25fb2952768aa6`

```json
{
 "id": "lem-pc-affine-model-limit-hom-equation-of-coherent-objects",
 "kind": "statement",
 "title": "Limit Hom equation from coherent object triangles",
 "statement": "Given the coherent comparison objects of lem-pc-affine-model-coherent-object-comparisons, the limit conjugated Hom equation of def-pc-affine-model-comparison-data holds for every chain map on the two scalar-extended models. This is only the limit-arrow portion of the argument; the other arrows and the construction of the object comparisons are not conclusions. The maps are scalarExtensionHom [def-pc-complex-scalar-extension-hom] and perfectStageMap/perfectLimitMap [lem-pc-perfect-hom-transport].",
 "source": {
  "document": "https://stacks.math.columbia.edu/tag/09RE",
  "place": "The explicit formula of def-pc-affine-model-comparison-data and the canonical termwise tilde definition; definitional constructor step."
 },
 "stmt_deps": [
  "lem-pc-affine-model-coherent-object-comparisons",
  "def-pc-complex-scalar-extension-hom",
  "lem-pc-perfect-hom-transport"
 ],
 "proof": [
  {
   "text": "Fix the arrow from j to the cocone point.\nApply naturality of the supplied full two-label comparison θ to the given chain\nmap a; it need not descend to the bottom. Scalar reassociation identifies\nscalarExtensionHom with κE.hom followed by extension of a followed by κK.inv,\nwhere κ is affineModelScalarAssocIso. The two object triangles express the\ncomparison at the target as κ, θ, pullback of the source comparison and the\ninverse perfectHomComparison. Substitute these formulas and expand map_comp.\nCancel adjacent inverse pairs, use naturality of θ, then cancel its inverse\npair. The result is exactly the conjugated Hom transport written below.\nProof irrelevance identifies the generated pullback-instance proofs with the\nnamed arrow representation. The argument includes identity arrows, zero rings,\nzero complexes and coincident labelled objects.",
   "uses": [
    "lem-pc-affine-model-coherent-object-comparisons",
    "def-pc-complex-scalar-extension-hom",
    "lem-pc-perfect-hom-transport"
   ],
   "elementary": true
  }
 ],
 "proof_origin": {
  "by": "agent",
  "document": "https://stacks.math.columbia.edu/tag/09RE",
  "place": "Definitional introduction of the explicitly stated affine comparison-data formula; source representations are given by real named functor definitions."
 },
 "mathlib_searches": [
  {
   "tool": "leansearch",
   "query": "Natural affine derived pullback comparison compatible with composition on K-flat complexes",
   "results": "Service unavailable: Internal Server Error",
   "date": "2026-10-14",
   "verdict": "unavailable"
  },
  {
   "tool": "leanfinder",
   "query": "Natural derived pullback comparison for K-flat module complexes along compatible affine scheme isomorphisms",
   "results": "Scheme.Modules.pullbackComp, pullbackSpecIso_hom_base and generic sheaf pullback results.",
   "date": "2026-10-14",
   "verdict": "No localized-coordinate model comparison or diagram propagation theorem."
  },
  {
   "tool": "loogle",
   "query": "ModuleCat.extendScalarsComp",
   "results": "extendScalarsComp and extendScalars_assoc provide associativity; no geometric model transport theorem.",
   "date": "2026-10-14",
   "verdict": "Use for the remaining coherence calculation."
  },
  {
   "tool": "grep",
   "query": "affineModelComparisonData|derivedPullback_tilde_kFlat_natIso|kFlat.*extendScalars|extendScalars.*kFlat",
   "results": "AffineDerivedPullbackTensorTilde has natural affine formulas; KFlatModuleBaseChange has the acyclic-tensor preservation criterion; no single-square comparison or propagation from bottom models.",
   "date": "2026-10-14",
   "verdict": "Use the existing affine and K-flat APIs and isolate only propagation."
  }
 ],
 "mathlib_match": null,
 "status": "split",
 "created": {
  "by": "worker",
  "item": "Sheaf.AlgebraicGeometry.AffineModelComparisonOfBottomModels",
  "date": "2026-10-14",
  "group": "P4"
 },
 "blueprint": {
  "is": null,
  "from": {
   "node": null,
   "place": "Limit arbitrary-chain-map naturality and reassociation step",
   "via": [
    "lem-pc-affine-model-comparison-of-bottom-models"
   ]
  },
  "same_as": []
 },
 "chapter": "sec-picard-framework",
 "unit": "sk-thm-picard-semicon",
 "lean": {
  "existing": false,
  "module": "Sheaf.AlgebraicGeometry.AffineModelLimitHomEquationOfCoherentObjects",
  "file": "lean/Sheaf/AlgebraicGeometry/AffineModelLimitHomEquationOfCoherentObjects.lean",
  "declaration": "AlgebraicGeometry.affineModelLimitHomEquation_of_coherent_objects",
  "declarations": [
   "AlgebraicGeometry.affineModelLimitHomEquation_of_coherent_objects"
  ],
  "statement": "theorem affineModelLimitHomEquation_of_coherent_objects {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (i : I) (Y : Scheme.{u}) [IsAffine Y] (s : Y ⟶ Spec (R.obj i)) [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] (P Q : schemeDerivedCategory Y) (F : Set.Ici i ⥤ CommRingCat.{u}) (C : Cocone F) (E K : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ) (d : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i), schemeDerivedCategory (Spec (F.obj j.val)) ≌ schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE j.val.property))))) (dlim : schemeDerivedCategory (Spec (C.pt)) ≌ schemeDerivedCategory (pullback s (Spec.map (c.ι.app i)))) (m : AffineModelCoherentObjects R c i Y s P Q F C E K d dlim) : ∀ (j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (a : ((Functor.mapHomologicalComplex (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ))).obj E ⟶ ((Functor.mapHomologicalComplex (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ))).obj K), m.βE.inv ≫ (affineModelLocalizedTilde C.pt _ dlim).map (CochainComplex.scalarExtensionHom (F.map (homOfLE j.property)).hom (C.ι.app j.val).hom (C.ι.app ⟨i, le_rfl⟩).hom (congrArg CommRingCat.Hom.hom (C.w (homOfLE j.property)).symm) E K a) ≫ m.βK.hom = perfectLimitMap R c s j.val.property ((m.αE j).inv ≫ (affineModelLocalizedTilde (F.obj j.val) _ (d j)).map a ≫ (m.αK j).hom)",
  "branch": "sheaf-dag",
  "by": "P4",
  "date": "2026-10-14"
 },
 "proof_deps": [
  "lem-pc-affine-model-coherent-object-comparisons",
  "def-pc-complex-scalar-extension-hom",
  "lem-pc-perfect-hom-transport"
 ],
 "reviewed": {
  "date": "2026-10-14",
  "by": "L",
  "reviewer": "COMPILER",
  "group": "P4",
  "result": "pass",
  "landing": "20261014T045611-L-1573878",
  "kind": "interface",
  "note": "new node of a stage-3 delivery, read against its source by the reviewer"
 },
 "reviewed_proof": {
  "date": "2026-10-14",
  "by": "L",
  "reviewer": "AUTO",
  "group": "U2",
  "result": "pass",
  "landing": "20261014T051908-L-1850389",
  "kind": "proof",
  "note": "AUTO: proofs only; landed in a batch after the tools' static checks; compiled with the probe by the group's delivery tool, verified by the global build (compile, axioms, sorry, 60 s per file); not read by a reviewer (stage 3, decision of the human 2026-10-12)",
  "sorry_before": [
   "AlgebraicGeometry.affineModelLimitHomEquation_of_coherent_objects"
  ],
  "sorry_after": []
 }
}
```

### Original snapshot: `dag/nodes/sec-picard-framework/lem-pc-affine-model-stage-hom-equation-of-coherent-objects.json`

SHA-256: `c1e12947380900495c1edea4197fec1812abc906d98ad64a1ca143ed7fd4c794`

```json
{
 "id": "lem-pc-affine-model-stage-hom-equation-of-coherent-objects",
 "kind": "statement",
 "title": "Stage Hom equation from coherent object triangles",
 "statement": "Given the coherent comparison objects of lem-pc-affine-model-coherent-object-comparisons, the stage conjugated Hom equation of def-pc-affine-model-comparison-data holds for every chain map on the two scalar-extended models. This is only the stage-arrow portion of the argument; the other arrows and the construction of the object comparisons are not conclusions. The maps are scalarExtensionHom [def-pc-complex-scalar-extension-hom] and perfectStageMap/perfectLimitMap [lem-pc-perfect-hom-transport].",
 "source": {
  "document": "https://stacks.math.columbia.edu/tag/09RE",
  "place": "The explicit formula of def-pc-affine-model-comparison-data and the canonical termwise tilde definition; definitional constructor step."
 },
 "stmt_deps": [
  "lem-pc-affine-model-coherent-object-comparisons",
  "def-pc-complex-scalar-extension-hom",
  "lem-pc-perfect-hom-transport"
 ],
 "proof": [
  {
   "text": "Fix the finite-stage arrow j→k.\nApply naturality of the supplied full two-label comparison θ to the given chain\nmap a; it need not descend to the bottom. Scalar reassociation identifies\nscalarExtensionHom with κE.hom followed by extension of a followed by κK.inv,\nwhere κ is affineModelScalarAssocIso. The two object triangles express the\ncomparison at the target as κ, θ, pullback of the source comparison and the\ninverse perfectHomComparison. Substitute these formulas and expand map_comp.\nCancel adjacent inverse pairs, use naturality of θ, then cancel its inverse\npair. The result is exactly the conjugated Hom transport written below.\nProof irrelevance identifies the generated pullback-instance proofs with the\nnamed arrow representation. The argument includes identity arrows, zero rings,\nzero complexes and coincident labelled objects.",
   "uses": [
    "lem-pc-affine-model-coherent-object-comparisons",
    "def-pc-complex-scalar-extension-hom",
    "lem-pc-perfect-hom-transport"
   ],
   "elementary": true
  }
 ],
 "proof_origin": {
  "by": "agent",
  "document": "https://stacks.math.columbia.edu/tag/09RE",
  "place": "Definitional introduction of the explicitly stated affine comparison-data formula; source representations are given by real named functor definitions."
 },
 "mathlib_searches": [
  {
   "tool": "leansearch",
   "query": "Natural affine derived pullback comparison compatible with composition on K-flat complexes",
   "results": "Service unavailable: Internal Server Error",
   "date": "2026-10-14",
   "verdict": "unavailable"
  },
  {
   "tool": "leanfinder",
   "query": "Natural derived pullback comparison for K-flat module complexes along compatible affine scheme isomorphisms",
   "results": "Scheme.Modules.pullbackComp, pullbackSpecIso_hom_base and generic sheaf pullback results.",
   "date": "2026-10-14",
   "verdict": "No localized-coordinate model comparison or diagram propagation theorem."
  },
  {
   "tool": "loogle",
   "query": "ModuleCat.extendScalarsComp",
   "results": "extendScalarsComp and extendScalars_assoc provide associativity; no geometric model transport theorem.",
   "date": "2026-10-14",
   "verdict": "Use for the remaining coherence calculation."
  },
  {
   "tool": "grep",
   "query": "affineModelComparisonData|derivedPullback_tilde_kFlat_natIso|kFlat.*extendScalars|extendScalars.*kFlat",
   "results": "AffineDerivedPullbackTensorTilde has natural affine formulas; KFlatModuleBaseChange has the acyclic-tensor preservation criterion; no single-square comparison or propagation from bottom models.",
   "date": "2026-10-14",
   "verdict": "Use the existing affine and K-flat APIs and isolate only propagation."
  }
 ],
 "mathlib_match": null,
 "status": "split",
 "created": {
  "by": "worker",
  "item": "Sheaf.AlgebraicGeometry.AffineModelComparisonOfBottomModels",
  "date": "2026-10-14",
  "group": "P4"
 },
 "blueprint": {
  "is": null,
  "from": {
   "node": null,
   "place": "Stage arbitrary-chain-map naturality and reassociation step",
   "via": [
    "lem-pc-affine-model-comparison-of-bottom-models"
   ]
  },
  "same_as": []
 },
 "chapter": "sec-picard-framework",
 "unit": "sk-thm-picard-semicon",
 "lean": {
  "existing": false,
  "module": "Sheaf.AlgebraicGeometry.AffineModelStageHomEquationOfCoherentObjects",
  "file": "lean/Sheaf/AlgebraicGeometry/AffineModelStageHomEquationOfCoherentObjects.lean",
  "declaration": "AlgebraicGeometry.affineModelStageHomEquation_of_coherent_objects",
  "declarations": [
   "AlgebraicGeometry.affineModelStageHomEquation_of_coherent_objects"
  ],
  "statement": "theorem affineModelStageHomEquation_of_coherent_objects {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (i : I) (Y : Scheme.{u}) [IsAffine Y] (s : Y ⟶ Spec (R.obj i)) [∀ Z : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] (P Q : schemeDerivedCategory Y) (F : Set.Ici i ⥤ CommRingCat.{u}) (C : Cocone F) (E K : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ) (d : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i), schemeDerivedCategory (Spec (F.obj j.val)) ≌ schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE j.val.property))))) (dlim : schemeDerivedCategory (Spec (C.pt)) ≌ schemeDerivedCategory (pullback s (Spec.map (c.ι.app i)))) (m : AffineModelCoherentObjects R c i Y s P Q F C E K d dlim) : ∀ (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k) (a : ((Functor.mapHomologicalComplex (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ))).obj E ⟶ ((Functor.mapHomologicalComplex (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ))).obj K), (m.αE k).inv ≫ (affineModelLocalizedTilde (F.obj k.val) _ (d k)).map (CochainComplex.scalarExtensionHom (F.map (homOfLE j.property)).hom (F.map (homOfLE hjk)).hom (F.map (homOfLE k.property)).hom (congrArg CommRingCat.Hom.hom (F.map_comp (homOfLE j.property) (homOfLE hjk))) E K a) ≫ (m.αK k).hom = perfectStageMap R s j.val.property hjk ((m.αE j).inv ≫ (affineModelLocalizedTilde (F.obj j.val) _ (d j)).map a ≫ (m.αK j).hom)",
  "branch": "sheaf-dag",
  "by": "P4",
  "date": "2026-10-14"
 },
 "proof_deps": [
  "lem-pc-affine-model-coherent-object-comparisons",
  "def-pc-complex-scalar-extension-hom",
  "lem-pc-perfect-hom-transport"
 ],
 "reviewed": {
  "date": "2026-10-14",
  "by": "L",
  "reviewer": "COMPILER",
  "group": "P4",
  "result": "pass",
  "landing": "20261014T045611-L-1573878",
  "kind": "interface",
  "note": "new node of a stage-3 delivery, read against its source by the reviewer"
 },
 "reviewed_proof": {
  "date": "2026-10-14",
  "by": "L",
  "reviewer": "COMPILER",
  "group": "P4",
  "result": "pass",
  "landing": "20261014T045611-L-1573878",
  "kind": "interface",
  "note": "AUTO: proofs only; landed in a batch after the tools' static checks; compiled with the probe by the group's delivery tool, verified by the global build (compile, axioms, sorry, 60 s per file); not read by a reviewer (stage 3, decision of the human 2026-10-12)"
 }
}
```

### Original snapshot: `dag/nodes/sec-picard-framework/lem-pc-kflat-extension-of-scalars.json`

SHA-256: `a61082644b8173269042d8ff586a0c8fe43837a71ea45bc3af660a5dfa13b737`

```json
{
 "id": "lem-pc-kflat-extension-of-scalars",
 "kind": "statement",
 "title": "Extension of scalars preserves K-flat module complexes",
 "statement": "Let A and B be commutative rings in the same universe, ρ:A→B a unital ring homomorphism, and K a Z-indexed cochain complex of A-modules. Assume that Tot(F⊗_A K) is acyclic for every acyclic A-complex F (ordinary-module K-flatness [def-pc-module-kflat-complex], using the total tensor construction [def-pc-tensor-complex-sheaves]). For every acyclic cochain complex L of B-modules, Tot(L⊗_B(B⊗_A K)) is acyclic. Extension of scalars is termwise Mathlib ModuleCat.extendScalars ρ, including its maps on differentials. No flatness, injectivity, or boundedness hypothesis is imposed on ρ or K.",
 "source": {
  "document": "literature/stacks-project/more-algebra.tex",
  "place": "Tag 06Y1, lemma-base-change-K-flat, proof; read at https://stacks.math.columbia.edu/tag/06Y1"
 },
 "stmt_deps": [
  "def-pc-module-kflat-complex",
  "def-pc-tensor-complex-sheaves"
 ],
 "proof": [
  {
   "text": "Restriction of scalars preserves and reflects exactness at every degree. Preservation applies ShortComplex.Exact.map; reflection applies ShortComplex.exact_map_iff_of_faithful. The ChangeOfRingsExact instances supply exactness preservation. These are proved as private acyclicity lemmas in the module.",
   "uses": [],
   "elementary": true
  },
  {
   "text": "Apply hK to the restricted L, using preservation of acyclicity. Use the tensor comparison isomorphism to transfer exactness at each degree to the restriction of the B-total tensor complex (HomologicalComplex.ExactAt.of_iso), then reflect acyclicity back to B.",
   "uses": [
    "lem-pc-tensor-restrict-extend-scalars"
   ],
   "elementary": true
  }
 ],
 "proof_deps": [
  "lem-pc-tensor-restrict-extend-scalars"
 ],
 "proof_origin": {
  "by": "document",
  "document": "literature/stacks-project/more-algebra.tex",
  "place": "Tag 06Y1, lemma-base-change-K-flat, proof; read at https://stacks.math.columbia.edu/tag/06Y1"
 },
 "mathlib_searches": [
  {
   "tool": "leansearch",
   "query": "extension of scalars preserves K flat complexes",
   "results": "Service unavailable: Internal Server Error.",
   "date": "2026-10-12",
   "verdict": "unavailable; no mathematical verdict"
  },
  {
   "tool": "leanfinder",
   "query": "extension of scalars of a K-flat complex along any ring homomorphism is K-flat",
   "results": "LeanFinder returned flat single-module stability and ModuleCat.preservesFiniteLimits_extendScalars_of_flat, no K-flat complex theorem. Loogle ModuleCat.extendScalars returned the functor, adjunction, counit and composition isomorphism, but no K-flatness theorem.",
   "date": "2026-10-12",
   "verdict": "no matching complex theorem"
  },
  {
   "tool": "grep",
   "query": "KFlat.*extendScalars|extendScalars.*KFlat",
   "results": "0 hits. Searches of the source library and all DAG nodes found only base-change arguments inside larger statements, not a standalone theorem.",
   "date": "2026-10-12",
   "verdict": "no matching complex theorem"
  }
 ],
 "mathlib_match": null,
 "status": "split",
 "created": {
  "by": "worker",
  "item": "Sheaf.Algebra.Homology.KFlatPullback",
  "date": "2026-10-12",
  "group": "R2"
 },
 "blueprint": {
  "is": null,
  "from": {
   "node": "lem-sc-finite-duality",
   "place": "derived pullback composition: step 3 of lem-pc-kflat-pullback-preservation, the ring-level Tag 06Y1 argument",
   "via": [
    "lem-pc-kflat-pullback-preservation",
    "lem-pc-ringed-spaces-derived-pullback-composition"
   ]
  },
  "same_as": []
 },
 "chapter": "sec-picard-framework",
 "unit": "sk-thm-picard-duality",
 "lean": {
  "existing": false,
  "module": "Sheaf.Algebra.Homology.KFlatModuleBaseChange",
  "file": "lean/Sheaf/Algebra/Homology/KFlatModuleBaseChange.lean",
  "declaration": "CochainComplex.acyclic_mapBifunctor_extendScalars_of_kFlat",
  "statement": "theorem acyclic_mapBifunctor_extendScalars_of_kFlat\n    {A B : Type u} [CommRing A] [CommRing B] (ρ : A →+* B)\n    (K : CochainComplex (ModuleCat.{u} A) ℤ)\n    (hK : ∀ F : CochainComplex (ModuleCat.{u} A) ℤ, F.Acyclic →\n      (mapBifunctor F K (curriedTensor _)).Acyclic)\n    (L : CochainComplex (ModuleCat.{u} B) ℤ) (hL : L.Acyclic) :\n    (mapBifunctor L\n      (((ModuleCat.extendScalars ρ).mapHomologicalComplex (.up ℤ)).obj K)\n      (curriedTensor _)).Acyclic",
  "branch": "sheaf-dag",
  "by": "R2",
  "date": "2026-10-12"
 },
 "reviewed": {
  "date": "2026-10-12",
  "by": "L",
  "reviewer": "COMPILER",
  "group": "R2",
  "result": "pass",
  "landing": "20261012T085327-L-35102",
  "kind": "interface",
  "note": "new node of a stage-3 delivery, read against its source by the reviewer"
 },
 "reviewed_proof": {
  "date": "2026-10-12",
  "by": "L",
  "reviewer": "COMPILER",
  "group": "U1",
  "result": "pass",
  "landing": "20261012T110320-L-622160",
  "kind": "interface",
  "note": "AUTO: proofs only; landed in a batch after the tools' static checks; compiled with the probe by the group's delivery tool, verified by the global build (compile, axioms, sorry, 60 s per file); not read by a reviewer (stage 3, decision of the human 2026-10-12)"
 }
}
```

### Original snapshot: `dag/nodes/sec-picard-framework/lem-pc-perfect-hom-transport.json`

SHA-256: `3035bad47e4896d3a43fc87933a30b1f8c2a98499f180d1bd03fee481b7da345`

```json
{
 "id": "lem-pc-perfect-hom-transport",
 "kind": "statement",
 "title": "Compatibility of canonical Hom transport with increasing a finite stage",
 "statement": "Let $I$ be a preordered set, $R:I\\to\\mathrm{CommRing}$ a diagram, $c$ a cocone, $i\\le j\\le k$, and $s:X\\to\\operatorname{Spec}(R_i)$ a scheme morphism [def-pc-scheme]. Assume derived categories exist [def-pc-derived-category]. Set $X_j=X\\times_{\\operatorname{Spec}(R_i)}\\operatorname{Spec}(R_j)$ and $X_\\infty=X\\times_{\\operatorname{Spec}(R_i)}\\operatorname{Spec}(c.pt)$. For objects $P,Q$ of $D(\\mathcal O_X)$ put $P_j=Lp_j^*P$, $Q_j=Lp_j^*Q$ [def-pc-derived-pullback]. For each transition $g$ define $C_g:Lp_{target}^*\\simeq Lg^*\\circ Lp_{source}^*$ using the fixed counit-pinned comparisons [lem-pc-ringed-spaces-derived-pullback-composition], and set $T_g(a)=C_g(Q)^{-1}\\circ Lg^*(a)\\circ C_g(P)$. Then for every $a:P_j\\to Q_j$, $T_{k,\\infty}(T_{j,k}(a))=T_{j,\\infty}(a)$. No perfectness, finite presentation or colimit hypothesis is imposed.",
 "source": {
  "document": "literature/stacks-project/cohomology.tex",
  "place": "Tag 0D5S, lemma-derived-pullback-composition; application to the base-change system of Tag 09RE"
 },
 "stmt_deps": [
  "def-pc-scheme",
  "def-pc-derived-category",
  "def-pc-derived-pullback",
  "lem-pc-ringed-spaces-derived-pullback-composition"
 ],
 "proof": [
  {
   "text": "The base-change maps compose by the pullback universal property and the cocone equation. Their composites with the projection to X equal the relevant direct projections. Apply the associativity law of the fixed derived-pullback comparisons to these three maps.",
   "uses": [
    "lem-pc-ringed-spaces-derived-pullback-composition"
   ],
   "elementary": false,
   "source": {
    "document": "literature/stacks-project/perfect.tex",
    "place": "Derived Categories of Schemes, Lemma 36.29.2, Tag 09RE, label lemma-descend-homomorphisms (full faithfulness), used in Lemma 36.29.3, Tag 09RF"
   }
  },
  {
   "text": "Evaluate at P and Q, use naturality at a, and cancel adjacent inverse-comparison components. This is exactly the equality of the conjugated Hom maps.",
   "uses": [],
   "elementary": true,
   "source": {
    "document": "literature/stacks-project/perfect.tex",
    "place": "Derived Categories of Schemes, Lemma 36.29.2, Tag 09RE, label lemma-descend-homomorphisms (full faithfulness), used in Lemma 36.29.3, Tag 09RF"
   }
  }
 ],
 "proof_deps": [
  "lem-pc-ringed-spaces-derived-pullback-composition"
 ],
 "proof_origin": {
  "by": "document",
  "document": "literature/stacks-project/cohomology.tex",
  "place": "Tag 0D5S, comparison associativity and naturality; explicit Lean conjugation and projection-equation proof by G1"
 },
 "mathlib_searches": [
  {
   "tool": "leansearch",
   "query": "derived pullback composition comparison associativity and conjugation of morphisms",
   "results": "Service returned Internal Server Error; unavailable",
   "date": "2026-10-13",
   "verdict": "unavailable"
  },
  {
   "tool": "leanfinder",
   "query": "associativity of derived pullback composition comparisons",
   "results": "Eight hits about ordinary categorical pullback comparisons; none about derived pullback coherence",
   "date": "2026-10-13",
   "verdict": "no match"
  },
  {
   "tool": "grep",
   "query": "derivedPullback.*[Cc]omp|pullback.*[Aa]ssoc",
   "results": "Underived sheaf/presheaf pullback_assoc and categorical pullback identities; no derived-pullback identity",
   "date": "2026-10-13",
   "verdict": "no match"
  }
 ],
 "mathlib_match": null,
 "status": "split",
 "created": {
  "by": "worker",
  "item": "Sheaf.AlgebraicGeometry.PerfectDescendMorphisms",
  "group": "G1",
  "date": "2026-10-13"
 },
 "blueprint": {
  "is": null,
  "from": {
   "node": "lem-pc-rf-perfect-base-change",
   "place": "Tag 09RF proof: full faithfulness for perfect complexes descends the overlap isomorphism and its inverse after increasing the index; Compatibility of canonical Hom transport with increasing a finite stage",
   "via": [
    "lem-pc-perfect-descend-morphisms"
   ]
  },
  "same_as": []
 },
 "lean_audit": {
  "master": {
   "state": "none"
  },
  "slopmaster2": {
   "state": "none"
  }
 },
 "chapter": "sec-picard-framework",
 "unit": "sk-thm-picard-semicon",
 "lean": {
  "existing": false,
  "module": "Sheaf.AlgebraicGeometry.PerfectHomTransport",
  "file": "lean/Sheaf/AlgebraicGeometry/PerfectHomTransport.lean",
  "declaration": "AlgebraicGeometry.perfectLimitMap_stage",
  "declarations": [
   "AlgebraicGeometry.perfectHomComposition",
   "AlgebraicGeometry.perfectHomComparison",
   "AlgebraicGeometry.perfectHomMap",
   "AlgebraicGeometry.perfectHomMap_id",
   "AlgebraicGeometry.perfectHomMap_comp",
   "AlgebraicGeometry.perfectHomMap_eq_iff",
   "AlgebraicGeometry.perfectStageMap",
   "AlgebraicGeometry.perfectLimitMap",
   "AlgebraicGeometry.perfectStageMap_id",
   "AlgebraicGeometry.perfectLimitMap_id",
   "AlgebraicGeometry.perfectLimitMap_stage",
   "AlgebraicGeometry.perfectHomMap_trans"
  ],
  "statement": "theorem perfectLimitMap_stage {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R) {i : I} {X : Scheme.{u}} (s : X ⟶ Spec (R.obj i)) {j k : I} (hij : i ≤ j) (hjk : j ≤ k) {P Q : schemeDerivedCategory X} (f : (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj P ⟶ (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj Q) : perfectLimitMap R c s (hij.trans hjk) (perfectStageMap R s hij hjk f) = perfectLimitMap R c s hij f",
  "branch": "sheaf-dag",
  "by": "G1",
  "date": "2026-10-13"
 },
 "reviewed": {
  "date": "2026-10-13",
  "by": "L",
  "reviewer": "X-aa353",
  "group": "G1",
  "result": "pass",
  "landing": "20261013T022414-L-3213338",
  "kind": "interface",
  "note": "new node of a stage-3 delivery, read against its source by the reviewer"
 },
 "reviewed_proof": {
  "date": "2026-10-13",
  "by": "L",
  "reviewer": "X-aa353",
  "group": "G1",
  "result": "pass",
  "landing": "20261013T022414-L-3213338",
  "kind": "interface",
  "note": "independent Codex review: Matched delivered Lean signatures and proofs with all three node records and Stacks 09RE/0D5S; all delivery modules and direct importer PerfectComplexDescent compile cleanly; comparison unchanged by rfl; axioms checked."
 }
}
```

### Original snapshot: `dag/nodes/sec-picard-framework/lem-pc-ringed-spaces-derived-pullback-composition.json`

SHA-256: `de2a8e79260ba83024bf08911e8f29082bbf3ea8be9abfd9f6cf6e1d8ee205ed`

```json
{
 "id": "lem-pc-ringed-spaces-derived-pullback-composition",
 "blueprint": {
  "is": null,
  "from": {
   "node": "lem-sc-finite-duality",
   "place": "the derived direct-image composition proof uses the canonical derived pullback composition and its identity and associativity coherence (Stacks Tag 0D5S)",
   "via": [
    "lem-pc-proper-derived-direct-image-composition"
   ]
  },
  "same_as": []
 },
 "kind": "statement",
 "title": "Composition of derived pullbacks",
 "statement": "Let $f:X\\to Y$ and $g:Y\\to Z$ be morphisms of schemes [def-pc-scheme] (more generally of ringed spaces). There is a canonical natural isomorphism $Lf^*\\circ Lg^*\\cong L(g\\circ f)^*$ of functors $D(\\mathcal O_Z)\\to D(\\mathcal O_X)$ [def-pc-derived-category], with derived pullback as in [def-pc-derived-pullback]. These isomorphisms are unital ($L(\\mathrm{id}_X)^*\\cong\\mathrm{id}$, compatibly with the composition isomorphisms) and associative: for a further morphism $h:W\\to X$ the two resulting isomorphisms $Lh^*\\circ Lf^*\\circ Lg^*\\cong L(g\\circ f\\circ h)^*$ coincide.",
 "source": {
  "document": "literature/stacks-project/cohomology.tex",
  "place": "Tag 0D5S, Cohomology Lemma cohomology-lemma-derived-pullback-composition"
 },
 "stmt_deps": [
  "def-pc-scheme",
  "def-pc-derived-category",
  "def-pc-derived-pullback",
  "lem-pc-module-pullback-adjunction"
 ],
 "proof": [
  {
   "text": "Extract the selected derived functor witness from exists_derivedPullback. Its object and map formulas identify the additive E with tensorPullback by Functor.ext. Transport the counit, universal property, and K-flat counit invertibility across this equality. Choose these witnesses for every f.",
   "uses": [
    "def-pc-derived-pullback"
   ],
   "elementary": false
  },
  {
   "text": "Apply the canonical-lift invertibility theorem for each f,g and form c(f,g) with asIso. Its hom is definitionally the required canonical leftDerivedLift.",
   "uses": [
    "lem-pc-derived-pullback-comparison-is-iso"
   ],
   "elementary": false
  },
  {
   "text": "Apply the coherence theorem to this c and its definitional hom equation to obtain i, both unit laws, and associativity. Package all witnesses.",
   "uses": [
    "lem-pc-derived-pullback-comparison-coherence"
   ],
   "elementary": false
  }
 ],
 "proof_deps": [
  "def-pc-derived-pullback",
  "lem-pc-derived-pullback-comparison-is-iso",
  "lem-pc-derived-pullback-comparison-coherence"
 ],
 "proof_origin": {
  "by": "document",
  "document": "literature/stacks-project/cohomology.tex",
  "place": "Tag 0D5S, Cohomology Lemma 20.27.2"
 },
 "mathlib_searches": [
  {
   "tool": "leanfinder",
   "query": "derived pullback Lf^* composed with Lg^* equals L(g compose f)^*",
   "results": "Only AlgebraicGeometry.Scheme.Modules.pullbackComp and related underived/sheaf declarations; no derived theorem.",
   "date": "2026-10-11",
   "verdict": "no match"
  },
  {
   "tool": "loogle",
   "query": "Functor.comp derived pullback",
   "results": "No usable hit.",
   "date": "2026-10-11",
   "verdict": "no match"
  },
  {
   "tool": "grep",
   "query": "pullbackComp|derived.*pullback",
   "results": "Underived pullbackComp declarations only; no derived ringed-space statement.",
   "date": "2026-10-11",
   "verdict": "no match"
  }
 ],
 "mathlib_match": null,
 "status": "split",
 "created": {
  "item": "lem-pc-proper-derived-direct-image-composition",
  "by": "worker",
  "date": "2026-10-10"
 },
 "chapter": "sec-picard-framework",
 "unit": "sk-thm-picard-duality",
 "split_report": {
  "date": "2026-10-11",
  "item": "lem-pc-ringed-spaces-derived-pullback-composition",
  "worker": "stage1",
  "summary": "Split Tag 0D5S into the K-flat derived-tensor construction of the canonical pullback composition isomorphism and the identity/associativity coherence obtained from tensor unitality and associativity. The resolution step cites the existing K-flat resolution lemma (Stacks 06YS) and the new K-flat pullback node lem-pc-kflat-pullback-preservation (Stacks 06YC).",
  "blueprint": "Realizes the derived pullback composition and coherence clause used in the direct-image composition proof.",
  "tool_uses": [
   {
    "node": "lem-pc-kflat-resolution",
    "why": "Step 1 uses its statement that every complex of O-modules on a site (here the open subsets of Z) has a K-flat resolution; this is a generic derived-tensor tool from the sk-thm-picard-semicon unit."
   }
  ]
 },
 "tool_uses": [
  "lem-pc-kflat-resolution",
  "lem-pc-kflat-resolution"
 ],
 "reviewed": {
  "date": "2026-10-10",
  "by": "L",
  "reviewer": "R-dpc1811",
  "group": "C1",
  "result": "pass",
  "note": "mechanical checks by tools/merge_delivery.py; mathematics reviewed in full by R-dpc1811 (reviewer sub-agent of L); spot-checked: Statement vs Stacks 0D5S (unit/assoc clauses added by E1 review are proved in Step 2 from tensor unitor/associator); new node lem-pc-kflat-pullback-preservation = Stacks 06YC, not a duplicate of lem-pur-kflat-change-of-rings (0G7E, change of rings only), Mathlib has no K-flat complexes; no cycle: def-pc-derived-pullback, the new node, lem-pc-kflat-resolution and lem-pc-ringed-spaces-derived-adjoint / lem-pc-derived-adjoint-functors (09T5) do not depend on the item. FIX more, RETURN less: (1) C1 Step 1 chose a K-flat resolution uncited -> cites lem-pc-kflat-resolution (06YS, declared tool use from sk-thm-picard-semicon), proof_deps updated; (2) split_report stale after the second reading: tool_uses named lem-pc-flat-complex-derived-pullback which no step cites (dropped) and summary said no new node -> rewritten.; 1 file(s) fixed by the reviewer"
 },
 "lean": {
  "module": "Sheaf.AlgebraicGeometry.DerivedPullbackComposition",
  "declaration": "AlgebraicGeometry.exists_derivedPullbackComposition",
  "declarations": [
   "AlgebraicGeometry.exists_derivedPullbackComposition"
  ],
  "file": "lean/Sheaf/AlgebraicGeometry/DerivedPullbackComposition.lean",
  "statement": "theorem exists_derivedPullbackComposition [d : ∀ X : Scheme.{u₁}, HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))] : ∃ (_ : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y), (Scheme.Modules.tensorPullback f).Additive) (ε : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y), DerivedCategory.Qh ⋙ derivedPullback f ⟶ (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace))) (_ : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y), (derivedPullback f).IsLeftDerivedFunctor (ε f) (HomotopyCategory.quasiIso (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))), ∃ c : ∀ {X Y Z : Scheme.{u₁}} (f : X ⟶ Y) (g : Y ⟶ Z), derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g), (∀ {X Y Z : Scheme.{u₁}} (f : X ⟶ Y) (g : Y ⟶ Z), (c f g).hom = (derivedPullback (f ≫ g)).leftDerivedLift (ε (f ≫ g)) (HomotopyCategory.quasiIso (SheafOfModules.{u₁} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ)) (derivedPullback g ⋙ derivedPullback f) ((Functor.associator DerivedCategory.Qh (derivedPullback g) (derivedPullback f)).inv ≫ Functor.whiskerRight (ε g) (derivedPullback f) ≫ (Functor.associator _ DerivedCategory.Qh (derivedPullback f)).hom ≫ Functor.whiskerLeft _ (ε f) ≫ (Functor.associator _ _ (DerivedCategory.Qh (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))).inv ≫ Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso ((conjugateIsoEquiv (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g))) ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm (Scheme.Modules.pushforwardComp f g).symm) (ComplexShape.up ℤ)).hom (DerivedCategory.Qh (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace))))) ∧ ∃ i : ∀ X : Scheme.{u₁}, derivedPullback (𝟙 X) ≅ 𝟭 _, (∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y), c (𝟙 X) f ≪≫ eqToIso (congrArg (fun k : X ⟶ Y => derivedPullback k) (Category.id_comp f)) = Functor.isoWhiskerLeft (derivedPullback f) (i X) ≪≫ Functor.rightUnitor (derivedPullback f)) ∧ (∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y), c f (𝟙 Y) ≪≫ eqToIso (congrArg (fun k : X ⟶ Y => derivedPullback k) (Category.comp_id f)) = Functor.isoWhiskerRight (i Y) (derivedPullback f) ≪≫ Functor.leftUnitor (derivedPullback f)) ∧ (∀ {W X Y Z : Scheme.{u₁}} (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z), Functor.isoWhiskerRight (c f g) (derivedPullback h) ≪≫ c h (f ≫ g) = Functor.associator (derivedPullback g) (derivedPullback f) (derivedPullback h) ≪≫ Functor.isoWhiskerLeft (derivedPullback g) (c h f) ≪≫ c (h ≫ f) g ≪≫ eqToIso (congrArg (fun k : W ⟶ Z => derivedPullback k) (Category.assoc h f g)))",
  "branch": "sheaf-dag",
  "by": "G1",
  "date": "2026-10-11",
  "existing": false,
  "fixed_by": "R-dpc1340"
 },
 "reviewed_lean": {
  "date": "2026-10-11",
  "by": "L",
  "reviewer": "R-dpc1340",
  "group": "G1",
  "result": "fix",
  "note": "schemes f:X->Y,g:Y->Z,h:W->X arbitrary; D(O) via recorded derivedPullback/schemeDerivedCategory with HasDerivedCategory family; c f g tied as leftDerivedLift of counits + conjugate of pushforwardComp; unit laws both sides; associativity both paths; ringed-space second derived pullback dropped; dropped duplicate new node(s) def-pc-ringed-space-derived-pullback (--drop-nodes; not merged, the item points at the landed declaration); left out new module(s) lean/Sheaf/AlgebraicGeometry/RingedSpaceDerivedPullback.lean (--drop-files, or a record fixed to existing: true)"
 },
 "lean_audit": {
  "master": {
   "state": "none",
   "decls": [],
   "missing": []
  },
  "slopmaster2": {
   "state": "none",
   "decls": [],
   "missing": []
  }
 },
 "reviewed_proof": {
  "date": "2026-10-12",
  "by": "L",
  "reviewer": "COMPILER",
  "group": "G1",
  "result": "pass",
  "landing": "20261012T085239-L-14766",
  "kind": "interface",
  "note": "AUTO: proofs only; landed in a batch after the tools' static checks; compiled with the probe by the group's delivery tool, verified by the global build (compile, axioms, sorry, 60 s per file); not read by a reviewer (stage 3, decision of the human 2026-10-12)"
 }
}
```

### Original snapshot: `dag/units/sk-thm-picard-semicon.json`

SHA-256: `c7d9481dc3dd3361dac03d9e316de00431aaf2a1e14cb6bfc1627f0a3c1a1571`

```json
{
 "id": "sk-thm-picard-semicon",
 "kind": "unit",
 "chapter": "sec-picard-framework",
 "title": "Semicontinuity and base change",
 "lean": [
  "AlgebraicGeometry.Scheme.Modules.upperSemicontinuous_hFiber"
 ],
 "uses": [
  "sk-def-av-jacobian",
  "sk-def-av-pic"
 ],
 "statement": "*Theorem (sketch).*\n\nWith $f$ and $\\cF$ as above, for every $t\\in T$ the function\n$t\\mapsto\\dim_{\\kappa(t)}H^q(X_t,\\cF_t)$ is upper semicontinuous in\n$t$, and there are canonical base-change maps\n$R^qf_*\\cF\\otimes\\kappa(t)\\to H^q(X_t,\\cF_t)$. If moreover $T$ is\n*reduced* and this function is locally constant, then $R^qf_*\\cF$ is\nfinite locally free (in particular flat) and the base-change maps in\ndegree $q$ are isomorphisms.",
 "steps": [
  {
   "text": "The standard semicontinuity theorem: the perfect complex $Rf_*\\mathcal F$\nsupplied by [sk-thm-picard-coherence](a) is, locally on $T$, represented by a\nbounded complex of finite free modules whose formation commutes with\nbase change, and the assertions follow from the flatness of the\nfamily together with the base-change comparison; the last clause is\nGrauert's theorem, which needs no Noetherian hypothesis: in the local\nmodel $K^\\bullet$ one has\n$\\dim_{\\kappa(t)}H^q(X_t,\\cF_t)=\\operatorname{rk}K^q-\\rho_q(t)-\\rho_{q-1}(t)$\nwith $\\rho_j(t)$ the rank of $d^j\\otimes\\kappa(t)$; each $\\rho_j$ is\nlower semicontinuous, so if their sum is locally constant both are, and\nover a *reduced* base a map of finite free modules whose fibre\nrank is locally constant has, locally and in suitable bases, the normal\nform $\\begin{pmatrix}I&0\\\\0&0\\end{pmatrix}$ (all larger minors vanish\nat every point, hence are nilpotent, hence zero). Thus\n$\\operatorname{im}d^{q-1}\\subseteq\\ker d^q$ are local direct summands\nof $K^q$, so $R^qf_*\\cF=\\ker d^q/\\operatorname{im}d^{q-1}$ is finite\nlocally free and its formation commutes with $\\otimes\\kappa(t)$, which\nis the isomorphism claim. Reducedness\ncannot be dropped: over $T=\\Spec k[\\varepsilon]/(\\varepsilon^2)$ let\n$\\cL$ be a line bundle on $E\\times_kT$, $E$ an elliptic curve, which\nrestricts to $\\cO_E$ but is a nontrivial first-order deformation of it;\nthen $H^0(\\cL)=\\varepsilon H^0(E,\\cO_E)\\cong k$ is killed by\n$\\varepsilon$, so it is not flat over $T$, although $T$ is a point."
  }
 ],
 "source": "literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-semicon/_section.md",
 "realized": {
  "statement": [],
  "steps": [
   []
  ]
 },
 "realized_by": null
}
```

### Original snapshot: `lean/Sheaf/Algebra/Homology/KFlatModuleBaseChange.lean`

SHA-256: `6dfe3267854906dd03d01dbf27d81f9421a1a6fd0f23143044f7f68a0cb4357c`

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Sheaf.Algebra.Homology.TensorRestrictExtendScalars
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-!
# K-flat base change over commutative rings

Source: Stacks Project, More on Algebra, Tag 06Y1.
(blueprint: lem-pc-kflat-extension-of-scalars)
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace CochainComplex

/-- Restriction of scalars reflects acyclicity of cochain complexes.
Source: Stacks Project, More on Algebra, Tag 06Y1, proof.
The underlying additive groups, kernels, and images are unchanged by restriction of scalars.
-/
private theorem acyclic_of_restrictScalars
    {A B : Type u} [CommRing A] [CommRing B] (ρ : A →+* B)
    (L : CochainComplex (ModuleCat.{u} B) ℤ)
    (hL : (((ModuleCat.restrictScalars ρ).mapHomologicalComplex (.up ℤ)).obj L).Acyclic) :
    L.Acyclic := by
  rw [HomologicalComplex.acyclic_iff] at hL ⊢
  intro i
  apply ((L.sc i).exact_map_iff_of_faithful (ModuleCat.restrictScalars ρ)).mp
  exact hL i

private theorem acyclic_restrictScalars
    {A B : Type u} [CommRing A] [CommRing B] (ρ : A →+* B)
    (L : CochainComplex (ModuleCat.{u} B) ℤ) (hL : L.Acyclic) :
    (((ModuleCat.restrictScalars ρ).mapHomologicalComplex (.up ℤ)).obj L).Acyclic := by
  intro i
  exact (hL i).map (ModuleCat.restrictScalars ρ)

/-- Extension of scalars preserves K-flatness without requiring the ring map to be flat.
Source: Stacks Project, More on Algebra, Tag 06Y1.
(blueprint: lem-pc-kflat-extension-of-scalars)

Proof: let `L` be an acyclic complex of `B`-modules. Restriction of scalars along `ρ`
is exact: kernels and images have the same underlying additive groups. Thus the
restricted `L` is acyclic over `A`. On pure tensors the maps
`l ⊗ (b ⊗ k) ↦ (b • l) ⊗ k` and `l ⊗ k ↦ l ⊗ (1 ⊗ k)` give inverse
isomorphisms between tensoring `L` over `B` with the extended `K` and tensoring
restricted `L` over `A` with `K`. They commute with each differential. Applying them
to every summand of total degree `n` gives inverse chain maps, including the sign
on the second differential. K-flatness of `K` makes the latter total complex
acyclic. The isomorphism and exactness of restriction of scalars give acyclicity
of the former total complex. This also covers zero rings and unbounded complexes:
there is no flatness hypothesis and each total degree uses a direct sum. -/
theorem acyclic_mapBifunctor_extendScalars_of_kFlat
    {A B : Type u} [CommRing A] [CommRing B] (ρ : A →+* B)
    (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : ∀ F : CochainComplex (ModuleCat.{u} A) ℤ, F.Acyclic →
      (mapBifunctor F K (curriedTensor _)).Acyclic)
    (L : CochainComplex (ModuleCat.{u} B) ℤ) (hL : L.Acyclic) :
    (mapBifunctor L
      (((ModuleCat.extendScalars ρ).mapHomologicalComplex (.up ℤ)).obj K)
      (curriedTensor _)).Acyclic := by
  apply acyclic_of_restrictScalars ρ
  obtain ⟨e⟩ := nonempty_tensorRestrictExtendScalarsIso ρ L K
  have h := hK _ (acyclic_restrictScalars ρ L hL)
  intro i
  exact (h i).of_iso e.symm

end CochainComplex
```

### Original snapshot: `lean/Sheaf/Algebra/Homology/ScalarExtensionHom.lean`

SHA-256: `106d50d9480988fb93583c819f6609e2b3909ee1667038c14ad2a99d2465f4d8`

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive

/-! # Scalar extension of maps between base-extended complexes

Source: Stacks Project, Derived Categories of Schemes, Tag 09RE, affine proof;
Mathlib's `ModuleCat.extendScalarsComp`
(blueprint: def-pc-complex-scalar-extension-hom).
-/

@[expose] public section

universe u₁

open CategoryTheory

namespace CochainComplex

/-- Extend a chain map over `S` between complexes extended from `R` to `T`, transporting
along the canonical associativity of extension of scalars and the equality `h = g.comp f`.
Source: Stacks Project, Derived Categories of Schemes, Tag 09RE, affine proof
(blueprint: def-pc-complex-scalar-extension-hom). -/
noncomputable def scalarExtensionHom
    {R S T : Type u₁} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (h : R →+* T) (hc : h = g.comp f)
    (P Q : CochainComplex (ModuleCat.{u₁} R) ℤ)
    (a : ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj Q) :
    ((ModuleCat.extendScalars h).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((ModuleCat.extendScalars h).mapHomologicalComplex (.up ℤ)).obj Q :=
  eqToHom (congrArg (fun t ↦
      ((ModuleCat.extendScalars t).mapHomologicalComplex (.up ℤ)).obj P) hc) ≫
    (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp f g) (.up ℤ)).hom.app P ≫
    ((ModuleCat.extendScalars g).mapHomologicalComplex (.up ℤ)).map a ≫
    (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp f g) (.up ℤ)).inv.app Q ≫
    eqToHom (congrArg (fun t ↦
      ((ModuleCat.extendScalars t).mapHomologicalComplex (.up ℤ)).obj Q) hc.symm)

end CochainComplex
```

### Original snapshot: `lean/Sheaf/AlgebraicGeometry/AffineDerivedPullbackTensorTilde.lean`

SHA-256: `48adfd48ad16b3d07596167dcb0d51cd96e827a55fc3e80b0819e0371844739c`

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde
import Sheaf.AlgebraicGeometry.TensorPullbackTilde
import Sheaf.AlgebraicGeometry.AffineTildeTotalTensor
import Sheaf.AlgebraicGeometry.KFlatDerivedTensorComparison
import Sheaf.Algebra.Homology.KFlatPullback
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.AlgebraicGeometry.DerivedPullbackTensorProduct
import Sheaf.AlgebraicGeometry.DerivedPullbackTensorComparisonDescent
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Affine computations of derived pullback and tensor

Source: Stacks Project, Lemmas 36.3.8(2), 36.3.9(2), Tags 08DW and 08DX,
and Lemma 36.3.6, Tag 08DV
(blueprint: lem-pc-affine-derived-pullback-tensor-tilde).

The affine formulas are written for every K-flat resolution `P ⟶ M`.
Thus the right sides are the concrete representatives of the module derived tensors,
with no boundedness, flatness of the ring map, or quasi-coherence hypothesis added.

## Main statements

- `derivedPullback_openRestriction_iso`: restriction of derived pullback.
- `derivedTensor_openRestriction_iso`: restriction of derived tensor, natural in both factors.
- `derivedPullback_tilde_iso`: affine pullback on any K-flat resolution.
- `derivedTensor_tilde_iso`: affine tensor on any K-flat resolution of the first factor.
- `derivedPullback_tilde_kFlat_natIso`: natural affine pullback comparison on K-flat models.
- `derivedTensor_tilde_kFlat_natIso`: natural affine tensor comparison on K-flat models.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry


attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private instance tilde_additive (A : Type u) [CommRing A] :
    (tilde.functor (.of A) : ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)).Additive :=
  ⟨by intros; exact tilde.map_add _ _⟩

private theorem tensorDerivedCounit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    ∃ (_ : (Scheme.Modules.tensorPullback f).Additive)
      (ε : DerivedCategory.Qh.{w} ⋙ derivedPullback f ⟶
        (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh.{w}
            (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))),
      (derivedPullback f).IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)) ∧
      ∀ P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
        CochainComplex.IsKFlat (R := Y.sheaf) P →
          IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := by
  have d := Classical.choose_spec (exists_derivedPullback f)
  obtain ⟨E, hE, hEmap, hEadd, ε, hL, htri, hK⟩ :=
    d.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2
  have h : E = Scheme.Modules.tensorPullback f :=
    CategoryTheory.Functor.ext hE (fun M N a ↦ hEmap a)
  subst E
  exact ⟨hEadd, ε, hL, hK⟩

private theorem pullbackCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] :
    Nonempty (derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g)) := by
  obtain ⟨ag, εg, hLg, hKg⟩ := tensorDerivedCounit g
  obtain ⟨af, εf, hLf, hKf⟩ := tensorDerivedCounit f
  obtain ⟨ac, εc, hLc, hKc⟩ := tensorDerivedCounit (f ≫ g)
  let := hLc
  obtain ⟨θ⟩ := Scheme.Modules.nonempty_tensorPullbackComp f g
  let β : DerivedCategory.Qh.{w} ⋙ (derivedPullback g ⋙ derivedPullback f) ⟶
      (Scheme.Modules.tensorPullback (f ≫ g)).mapHomotopyCategory (.up ℤ) ⋙
        (DerivedCategory.Qh.{w}
          (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))) :=
    (Functor.associator DerivedCategory.Qh.{w} (derivedPullback g)
      (derivedPullback f)).inv ≫
    Functor.whiskerRight εg (derivedPullback f) ≫
    (Functor.associator _ DerivedCategory.Qh.{w} (derivedPullback f)).hom ≫
    Functor.whiskerLeft _ εf ≫
    (Functor.associator _ _
      (DerivedCategory.Qh.{w} (C := SheafOfModules.{u}
        (moduleRings X.toRingedSpace)))).inv ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso θ.symm (.up ℤ)).hom
      (DerivedCategory.Qh.{w} (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))
  let τ := (derivedPullback (f ≫ g)).leftDerivedLift εc
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (.up ℤ))
    (derivedPullback g ⋙ derivedPullback f) β
  have hflat (P : CochainComplex
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ)
      (hP : CochainComplex.IsKFlat (R := Z.sheaf) P) :
      IsIso (τ.app (DerivedCategory.Qh.{w}.obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) := by
    have hg := hKg P hP
    have hfg := hKc P hP
    have hPg : CochainComplex.IsKFlat (R := Y.sheaf)
        (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P) := by
      exact CochainComplex.isKFlat_pullback g.base Y.sheaf Z.sheaf ⟨g.c⟩ P hP
    have hf := hKf _ hPg
    have hfapp : IsIso (εf.app
        (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) := by
      rw [Functor.mapHomotopyCategory_obj]
      exact hf
    have fac := (derivedPullback (f ≫ g)).leftDerived_fac_app εc
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (.up ℤ))
      (derivedPullback g ⋙ derivedPullback f) β
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
    have : IsIso (τ.app (DerivedCategory.Qh.{w}.obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
          εc.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
      rw [show τ.app _ ≫ _ = _ from fac]
      dsimp only [β, NatTrans.comp_app, Functor.associator_inv_app,
        Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
      have h1 : IsIso ((derivedPullback f).map
          (εg.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) := inferInstance
      have h2 : IsIso ((DerivedCategory.Qh.{w}
          (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).map
          ((Functor.mapHomotopyCategoryCompIso θ.symm (.up ℤ)).hom.app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) := inferInstance
      simp only [Category.id_comp]
      exact IsIso.comp_isIso' h1 (IsIso.comp_isIso' hfapp h2)
    exact IsIso.of_isIso_comp_right _ (εc.app _)
  have : IsIso τ := by
    apply (NatTrans.isIso_iff_isIso_app τ).2
    intro K
    let Q := DerivedCategory.Qh.{w}
      (C := SheafOfModules.{u} (moduleRings Z.toRingedSpace))
    apply (NatTrans.isIso_app_iff_of_iso τ (Q.objObjPreimageIso K)).1
    obtain ⟨G, hG⟩ := HomotopyCategory.quotient_obj_surjective (Q.objPreimage K)
    rw [← hG]
    obtain ⟨P, s, hP, _, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolution (R := Z.sheaf) G
    have hsq := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs
    have := Localization.inverts Q (HomotopyCategory.quasiIso _ (.up ℤ)) _ hsq
    apply (NatTrans.isIso_app_iff_of_iso τ
      (asIso (Q.map ((HomotopyCategory.quotient _ (.up ℤ)).map s)))).1
    exact hflat P hP
  exact ⟨asIso τ⟩

private theorem pullbackOpenIso (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))] :
    let R : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
      (Scheme.Modules.overEquiv U).functor
    Nonempty (derivedPullback U.ι ≅ Functor.mapDerivedCategory.{w, w} R) := by
  dsimp only
  let R : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
    (Scheme.Modules.overEquiv U).functor
  obtain ⟨a, ε, hL, _⟩ := tensorDerivedCounit U.ι
  let := hL
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction U.ι
  let θ : Scheme.Modules.tensorPullback U.ι ≅ R :=
    adj.leftAdjointUniq (Scheme.Modules.restrictAdjunction U.ι) ≪≫
      (Scheme.Modules.overFunctorEquiv U).symm
  have : R.Additive := by dsimp [R]; infer_instance
  have : PreservesFiniteLimits R := by dsimp [R]; infer_instance
  have : PreservesFiniteColimits R := by dsimp [R]; infer_instance
  let θh : (Scheme.Modules.tensorPullback U.ι).mapHomotopyCategory (.up ℤ) ≅
      R.mapHomotopyCategory (.up ℤ) :=
    { hom := θ.hom.mapHomotopyCategory (.up ℤ)
      inv := θ.inv.mapHomotopyCategory (.up ℤ)
      hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp, θ.hom_inv_id]; rfl
      inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp, θ.inv_hom_id]; rfl }
  let δ := Functor.isoWhiskerRight θh
    (DerivedCategory.Qh.{w} (C := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)))
  let α := (Functor.mapDerivedCategoryFactorsh.{w, w} R) ≪≫ δ.symm
  have := Functor.isLeftDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ))
    (Functor.mapDerivedCategory.{w, w} R) α
  exact ⟨Functor.leftDerivedUnique (Functor.mapDerivedCategory.{w, w} R) (derivedPullback U.ι)
    ε α.hom (HomotopyCategory.quasiIso _ (.up ℤ))⟩

/-- Derived pullback commutes naturally with restriction to opens.
Source: Stacks, Tag 08DW, proof
(blueprint: lem-pc-affine-derived-pullback-tensor-tilde).
Proof (node step 1): choose a K-flat resolution on Y (lem-pc-kflat-resolution).
Restriction to V preserves K-flatness (lem-pc-kflat-pullback-preservation).
Termwise tensor pullback and restriction commute, so both composite functors are
computed by the same pulled-back restricted resolution (def-pc-derived-pullback).
The resolution comparison is natural and descends to the derived category. -/
theorem derivedPullback_openRestriction_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : X.Opens) (V : Y.Opens) (hUV : U ≤ f ⁻¹ᵁ V)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))] :
    Nonempty (derivedPullback f ⋙
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)).mapDerivedCategory ≅
      (SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) V ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))
          (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv V)).mapDerivedCategory ⋙
        derivedPullback (f.resLE V U hUV)) := by
  obtain ⟨a⟩ := pullbackOpenIso X U
  obtain ⟨b⟩ := pullbackOpenIso Y V
  obtain ⟨c⟩ := pullbackCompIso U.ι f
  obtain ⟨d⟩ := pullbackCompIso (f.resLE V U hUV) V.ι
  refine ⟨Functor.isoWhiskerLeft (derivedPullback f) a.symm ≪≫ c ≪≫ ?_ ≪≫
    d.symm ≪≫ Functor.isoWhiskerRight b (derivedPullback (f.resLE V U hUV))⟩
  exact eqToIso (congrArg (fun k ↦ derivedPullback k) (Scheme.Hom.resLE_comp_ι f hUV).symm)

/-- Derived tensor commutes with restriction to any open subscheme.
Source: Stacks, Tag 08DX, proof; the restriction computation of Tag 08DW
(blueprint: lem-pc-affine-derived-pullback-tensor-tilde).
Proof (node step 1): choose a K-flat resolution of K (lem-pc-kflat-resolution).
It remains K-flat on U (lem-pc-kflat-pullback-preservation). Restriction commutes
with sheaf tensor and all direct sums in the signed total complex
(def-pc-tensor-complex-sheaves), so it identifies the two derived tensors.
The comparisons are induced by restriction of the total tensor complex. -/
theorem derivedTensor_openRestriction_iso (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    : Nonempty
      (curriedTensor (schemeDerivedCategory X) ⋙
        (Functor.whiskeringRight (schemeDerivedCategory X) (schemeDerivedCategory X)
          (schemeDerivedCategory U.toScheme)).obj
          (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U)).mapDerivedCategory ≅
        (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U)).mapDerivedCategory ⋙
          curriedTensor (schemeDerivedCategory U.toScheme) ⋙
          (Functor.whiskeringLeft (schemeDerivedCategory X)
            (schemeDerivedCategory U.toScheme) (schemeDerivedCategory U.toScheme)).obj
            (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U)).mapDerivedCategory) := by
  obtain ⟨F, hF, hmap, hadd, ε, hε, φ, _, hnat, hiso⟩ :=
    derivedPullback_tensorProduct U.ι
  obtain ⟨μ, _⟩ := derivedPullback_tensor_comparison_exists U.ι F hF hmap ε hε
    φ hnat hiso
  obtain ⟨a⟩ := pullbackOpenIso X U
  exact ⟨(curriedTensorPostFunctor.mapIso a).symm ≪≫ μ.symm ≪≫
    curriedTensorPreFunctor.mapIso a⟩

private theorem moduleKFlat_acyclic (A : Type u) [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P)
    (F : CochainComplex (ModuleCat.{u} A) ℤ) (hF : F.Acyclic) :
    (CochainComplex.mapBifunctor F P (curriedTensor (ModuleCat.{u} A))).Acyclic := by
  have h := (HomotopyCategory.kFlat_iff_preserves_acyclic
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)).mp
      ((HomotopyCategory.kFlat_quotient_obj_iff P).mpr hP)
  have hF' := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic F).mpr hF
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mp
    (h _ hF').2

private theorem counitComparison
    {C D I : Type*} [Category C] [Category D] [Category I]
    [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    (E₀ : C ⥤ D) [E₀.Additive]
    (L : DerivedCategory.{w} C ⥤ DerivedCategory.{w} D)
    (F : I ⥤ CochainComplex C ℤ)
    (ε : DerivedCategory.Qh.{w} ⋙ L ⟶
      E₀.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh.{w})
    [IsIso (Functor.whiskerLeft (F ⋙ HomotopyCategory.quotient _ (.up ℤ)) ε)] :
    Nonempty (F ⋙ DerivedCategory.Q.{w} ⋙ L ≅
      F ⋙ E₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w}) := by
  exact ⟨ Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft F (DerivedCategory.quotientCompQhIso _).symm) L ≪≫
    asIso (Functor.whiskerLeft (F ⋙ HomotopyCategory.quotient _ (.up ℤ)) ε) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft F
        (E₀.mapHomotopyCategoryFactors (.up ℤ)))
      DerivedCategory.Qh ≪≫
    Functor.isoWhiskerLeft (F ⋙ E₀.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso _)⟩

private theorem baseChangeCounitComparison
    {A₀ B₀ C D I : Type*}
    [Category A₀] [Category B₀] [Category C] [Category D] [Category I]
    [Preadditive A₀] [Preadditive B₀] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    (T : A₀ ⥤ C) (S : B₀ ⥤ D) (H : A₀ ⥤ B₀) (E : C ⥤ D)
    [T.Additive] [S.Additive] [H.Additive] [E.Additive]
    (L : DerivedCategory.{w} C ⥤ DerivedCategory.{w} D)
    (F : I ⥤ CochainComplex A₀ ℤ)
    (ε : DerivedCategory.Qh.{w} ⋙ L ⟶
      E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh.{w})
    (θ : T ⋙ E ≅ H ⋙ S)
    (hε : ∀ P, IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
      ((T.mapHomologicalComplex (.up ℤ)).obj (F.obj P))))) :
    Nonempty (F ⋙ T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⋙ L ≅
      F ⋙ H.mapHomologicalComplex (.up ℤ) ⋙ S.mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q.{w}) := by
  have : IsIso (Functor.whiskerLeft
      ((F ⋙ T.mapHomologicalComplex (.up ℤ)) ⋙ HomotopyCategory.quotient _ (.up ℤ)) ε) :=
    (NatTrans.isIso_iff_isIso_app _).2 hε
  obtain ⟨β⟩ := counitComparison E L (F ⋙ T.mapHomologicalComplex (.up ℤ)) ε
  let δ : T.mapHomologicalComplex (.up ℤ) ⋙ E.mapHomologicalComplex (.up ℤ) ≅
      H.mapHomologicalComplex (.up ℤ) ⋙ S.mapHomologicalComplex (.up ℤ) :=
    Functor.mapHomologicalComplexCompIso θ (.up ℤ)
  exact ⟨β ≪≫ Functor.isoWhiskerLeft F
    (Functor.isoWhiskerRight δ DerivedCategory.Q.{w})⟩

/-- Naturality of the affine pullback comparison on K-flat module models.
Source: Stacks, Tag 08DW(2), via Tag 08DV
(blueprint: lem-pc-affine-derived-pullback-tensor-tilde).
Proof (node step 2): apply the natural termwise tilde/base-change isomorphism
(lem-weil-pbc-tilde-pullback-base-change) to K-flat complexes. Their tilde complexes
are K-flat (lem-pc-affine-tilde-kflat), so the derived-pullback counit is invertible
there (def-pc-derived-pullback). Compose the two natural comparisons. For arbitrary
M use a K-flat resolution P to M; exact tilde sends it to an isomorphism after Q
(lem-pc-affine-qcoh-derived-equivalence). Naturality on K-flat models gives compatibility
with resolution comparisons, hence the affine formula independent of that choice. -/
theorem derivedPullback_tilde_kFlat_natIso (A B : Type u) [CommRing A] [CommRing B]
    (φ : A →+* B)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace))] :
    Nonempty
      (CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙
        (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙
          DerivedCategory.Q ⋙ derivedPullback (Spec.map (CommRingCat.ofHom φ)) ≅
        CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙
          (ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ) ⋙
          (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} B ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace))
            (tilde.functor (.of B))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙ DerivedCategory.Q) := by
  let f := Spec.map (CommRingCat.ofHom φ)
  obtain ⟨hEadd, ε, hε, hflat⟩ := tensorDerivedCounit f
  obtain ⟨θ, _⟩ := Scheme.Modules.exists_tensorPullback_tilde_iso (CommRingCat.ofHom φ)
  let TA : ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) := tilde.functor (.of A)
  let TB : ModuleCat.{u} B ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace) := tilde.functor (.of B)
  have : TA.Additive := tilde_additive A
  have : TB.Additive := tilde_additive B
  apply baseChangeCounitComparison TA TB
    (ModuleCat.extendScalars φ) (Scheme.Modules.tensorPullback f)
    (derivedPullback f) (CochainComplex.ιKFlat (ModuleCat.{u} A)) ε θ
  intro P
  apply hflat
  exact isKFlat_tilde A P.obj (moduleKFlat_acyclic A P.obj P.property)

/-- Naturality of the affine tensor comparison in a K-flat first model and an arbitrary
second complex. Source: Stacks, Tag 08DX(2), via Tag 08DV
(blueprint: lem-pc-affine-derived-pullback-tensor-tilde).
Proof (node step 3): tilde of the first model is K-flat (lem-pc-affine-tilde-kflat).
Compute sheaf derived tensor by that model (def-pc-kflat-complex). Apply the natural
tilde/tensor isomorphism in each bidegree (lem-weil-pbc-affine-tilde-tensor), then
preservation of arbitrary coproducts by tilde, to obtain the total-complex comparison
(def-pc-tensor-complex-sheaves). All maps commute with both differentials and with
maps in both variables. Resolve an arbitrary first complex (lem-pc-kflat-resolution);
exactness of tilde (lem-pc-affine-qcoh-derived-equivalence) and naturality give the
comparison for it, independently of the chosen resolution. -/
theorem derivedTensor_tilde_kFlat_natIso (A : Type u) [CommRing A]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))] :
    Nonempty
      (CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙
        (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙ DerivedCategory.Q ⋙
          curriedTensor (schemeDerivedCategory (Spec (.of A))) ⋙
          (Functor.whiskeringLeft (CochainComplex (ModuleCat.{u} A) ℤ)
            (schemeDerivedCategory (Spec (.of A)))
            (schemeDerivedCategory (Spec (.of A)))).obj
            ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙ DerivedCategory.Q) ≅
        CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙
          (curriedTensor (ModuleCat.{u} A)).map₂CochainComplex ⋙
          (Functor.whiskeringRight (CochainComplex (ModuleCat.{u} A) ℤ)
            (CochainComplex (ModuleCat.{u} A) ℤ)
            (schemeDerivedCategory (Spec (.of A)))).obj
            ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙ DerivedCategory.Q)) := by
  let T := @Functor.mapHomologicalComplex _ _ _ _ _ _ _
    (@id (ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
      (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)
  let F := CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙ T
  have hβ := kFlat_derivedTensor_comparison_natIso (Spec (.of A)) F T
    (fun P ↦ isKFlat_tilde A P.obj (moduleKFlat_acyclic A P.obj P.property))
  have hθ := affineTilde_totalTensor_natIso A
  refine Nonempty.map2 ?_ hβ hθ
  intro β θ
  let ι := CochainComplex.ιKFlat (ModuleCat.{u} A)
  exact (Functor.associator ι T _).symm ≪≫ β ≪≫
    Functor.associator ι T _ ≪≫ Functor.isoWhiskerLeft ι θ



private theorem affineTilde_Q_map_isIso (A : Type u) [CommRing A]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    {P M : CochainComplex (ModuleCat.{u} A) ℤ} (s : P ⟶ M) (hs : QuasiIso s) :
    IsIso (DerivedCategory.Q.map
      (((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ))).map s)) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  obtain ⟨e, ⟨α⟩, _⟩ := exists_affineQCohDerivedEquivalence A
  have : QuasiIso s := hs
  exact (NatIso.isIso_map_iff α s).mp (by
    change IsIso (((e.functor ⋙ (schemeDerivedQCohProperty (Spec (.of A))).ι).map
      (DerivedCategory.Q.map s)))
    infer_instance)

private theorem mapIso_trans_nonempty
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {P M : C} {N : D} (s : P ⟶ M) [IsIso s] (e : F.obj P ≅ N) :
    Nonempty (F.obj M ≅ N) :=
  ⟨F.mapIso (asIso s).symm ≪≫ e⟩

private theorem tensorIso_trans_nonempty
    {C : Type*} [Category C] [MonoidalCategory C]
    {P M N R : C} (s : P ⟶ M) [IsIso s] (e : P ⊗ N ≅ R) :
    Nonempty (M ⊗ N ≅ R) :=
  ⟨tensorIso (asIso s).symm (Iso.refl N) ≪≫ e⟩

/-- Affine derived pullback of termwise tilde is termwise tilde of derived base change,
computed on any K-flat resolution of the input complex.
Source: Stacks, Tag 08DW(2), via Tag 08DV
(blueprint: lem-pc-affine-derived-pullback-tensor-tilde).
Proof (node step 2): resolve M by P (lem-pc-kflat-resolution). Termwise tilde
preserves quasi-isomorphisms (lem-pc-affine-qcoh-derived-equivalence), and tilde P
is K-flat (lem-pc-affine-tilde-kflat). Derived pullback is therefore represented
by termwise tensor pullback of tilde P (def-pc-derived-pullback).
The natural tilde/base-change comparison in each degree
(lem-weil-pbc-tilde-pullback-base-change) identifies this with tilde of B tensor P.
This complex computes M tensor-derived B since P is K-flat. -/
theorem derivedPullback_tilde_iso (A B : Type u) [CommRing A] [CommRing B]
    (φ : A →+* B)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace))]
    (M P : CochainComplex (ModuleCat.{u} A) ℤ) (s : P ⟶ M) (hs : QuasiIso s)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P) :
    Nonempty
      ((derivedPullback (Spec.map (CommRingCat.ofHom φ))).obj
        (DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
            (@id (ModuleCat.{u} A ⥤
              SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
              (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)) ≅
        DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
            (@id (ModuleCat.{u} B ⥤
              SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace))
              (tilde.functor (.of B))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj
                (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P))) := by
  let T := @Functor.mapHomologicalComplex _ _ _ _ _ _ _
    (@id (ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
      (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)
  have : IsIso (DerivedCategory.Q.map (T.map s)) := affineTilde_Q_map_isIso A s hs
  obtain ⟨α⟩ := derivedPullback_tilde_kFlat_natIso A B φ
  exact mapIso_trans_nonempty (derivedPullback (Spec.map (CommRingCat.ofHom φ)))
    (DerivedCategory.Q.map (T.map s)) (α.app ⟨P, hP⟩)

/-- On an affine scheme, derived tensor of termwise tilde complexes is termwise tilde
of module derived tensor, computed with any K-flat resolution of the first factor.
Source: Stacks, Tag 08DX(2), via Tag 08DV
(blueprint: lem-pc-affine-derived-pullback-tensor-tilde).
Proof (node step 3): resolve M by P (lem-pc-kflat-resolution). Exactness of termwise
tilde (lem-pc-affine-qcoh-derived-equivalence) and K-flatness of tilde P
(lem-pc-affine-tilde-kflat) allow the sheaf derived tensor to be computed by
Tot(tilde P tensor tilde N) (def-pc-kflat-complex, def-pc-tensor-complex-sheaves).
In each bidegree apply lem-weil-pbc-affine-tilde-tensor; its naturality respects
both differentials. Tilde preserves the direct sums used in totalization, yielding
tilde Tot(P tensor N). This computes M tensor-derived N since P is K-flat.
The sum over p+q=n can be infinite for unbounded complexes; all coproducts, not just
finite ones, are preserved by tilde, which is a left adjoint. -/
theorem derivedTensor_tilde_iso (A : Type u) [CommRing A]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (M N P : CochainComplex (ModuleCat.{u} A) ℤ) (s : P ⟶ M) (hs : QuasiIso s)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P) :
    Nonempty
      (DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M) ⊗
        DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
            (@id (ModuleCat.{u} A ⥤
              SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
              (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj N) ≅
        DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
            (@id (ModuleCat.{u} A ⥤
              SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
              (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj
                (CochainComplex.mapBifunctor P N (curriedTensor (ModuleCat.{u} A))))) := by
  let T := @Functor.mapHomologicalComplex _ _ _ _ _ _ _
    (@id (ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
      (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)
  have : IsIso (DerivedCategory.Q.map (T.map s)) := affineTilde_Q_map_isIso A s hs
  obtain ⟨α⟩ := derivedTensor_tilde_kFlat_natIso A
  exact tensorIso_trans_nonempty (DerivedCategory.Q.map (T.map s))
    ((α.app ⟨P, hP⟩).app N)


end AlgebraicGeometry
```

### Original snapshot: `lean/Sheaf/AlgebraicGeometry/AffineModelCoherentObjectComparisons.lean`

SHA-256: `6b6ce51929992341008fc41b4ddb606df8468e0a91c18753df488a20d01453cb`

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectHomTransport
public import Sheaf.Algebra.Homology.ScalarExtensionHom
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.InducedCategory
import Sheaf.Algebra.Homology.KFlatModuleBaseChange

/-! # Coherent affine object comparisons
Source: Stacks Project, Tags 09RE, 06Y1 and 0D5S.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/

@[expose] public section
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Termwise tilde on module complexes, with its zero-map proof fixed once.
Source: Mathlib's tilde.functor and Functor.mapHomologicalComplex.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
noncomputable abbrev affineModelTildeComplex (A : CommRingCat.{u}) :
    CochainComplex (ModuleCat.{u} A) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace)) ℤ :=
  @Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
    (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace))
    _ _ _ _ (@id (ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace)) (tilde.functor A))
    ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)

/-- Localization of termwise tilde followed by the supplied coordinate equivalence.
Source: the defining affine comparison functor in Stacks, Tag 09RE.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
noncomputable def affineModelLocalizedTilde (A : CommRingCat.{u}) (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (d : schemeDerivedCategory (Spec A) ≌ schemeDerivedCategory X) :
    CochainComplex (ModuleCat.{u} A) ℤ ⥤ schemeDerivedCategory X where
  obj M := d.functor.obj (DerivedCategory.Q.obj ((affineModelTildeComplex A).obj M))
  map f := d.functor.map (DerivedCategory.Q.map ((affineModelTildeComplex A).map f))
  map_id M := by simp
  map_comp f g := by simp

/-- The map equation of the localized tilde functor, without unfolding its functor record.
Source: the explicit localized tilde construction.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
theorem affineModelLocalizedTilde_map (A : CommRingCat.{u}) (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (d : schemeDerivedCategory (Spec A) ≌ schemeDerivedCategory X)
    {M N : CochainComplex (ModuleCat.{u} A) ℤ} (f : M ⟶ N) :
    (affineModelLocalizedTilde A X d).map f =
      d.functor.map (DerivedCategory.Q.map ((affineModelTildeComplex A).map f)) := by
  rfl

/-- The two scalar-extended models, with labels retained when they coincide.
Source: Mathlib's induced category; Stacks, Tag 09RE.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
noncomputable abbrev affineModelScalarPair {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (E K : CochainComplex (ModuleCat.{u} A) ℤ) (q : Bool) :
    CochainComplex (ModuleCat.{u} B) ℤ :=
  cond q (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj E)
    (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj K)

/-- Scalar-extension reassociation, including the specified equality of ring maps.
Source: Stacks Project, Tag 09RE; `ModuleCat.extendScalarsComp`.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
@[irreducible]
noncomputable def affineModelScalarAssocIso
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (hc : h = g.comp f)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((ModuleCat.extendScalars h).mapHomologicalComplex (.up ℤ)).obj M ≅
      ((ModuleCat.extendScalars g).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj M) :=
  eqToIso (congrArg (fun t ↦
    ((ModuleCat.extendScalars t).mapHomologicalComplex (.up ℤ)).obj M) hc) ≪≫
      (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp f g) (.up ℤ)).app M

/-- The forward scalar reassociation map, from its explicit construction. -/
theorem affineModelScalarAssocIso_hom
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (hc : h = g.comp f)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    (affineModelScalarAssocIso f g h hc M).hom =
      eqToHom (congrArg (fun t ↦
        ((ModuleCat.extendScalars t).mapHomologicalComplex (.up ℤ)).obj M) hc) ≫
          (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp f g) (.up ℤ)).hom.app M := by
  unfold affineModelScalarAssocIso
  rfl

/-- The inverse scalar reassociation map, from its explicit construction. -/
theorem affineModelScalarAssocIso_inv
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (hc : h = g.comp f)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    (affineModelScalarAssocIso f g h hc M).inv =
      (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp f g) (.up ℤ)).inv.app M ≫
        eqToHom (congrArg (fun t ↦
          ((ModuleCat.extendScalars t).mapHomologicalComplex (.up ℤ)).obj M) hc.symm) := by
  unfold affineModelScalarAssocIso
  rfl

/-- The finite-stage base arrow in the over category.
Source: Spec functoriality; Stacks, Tag 09RE.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
noncomputable abbrev affineModelStageArrow {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) {i : I}
    (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k) :
    Over.mk (Spec.map (R.map (homOfLE k.val.property))) ⟶
      Over.mk (Spec.map (R.map (homOfLE j.val.property))) :=
  Over.homMk (Spec.map (R.map (homOfLE hjk)))
    (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)

/-- The arrow from the cocone spectrum to a finite-stage spectrum.
Source: Spec functoriality and cocone naturality; Stacks, Tag 09RE.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
noncomputable abbrev affineModelLimitArrow {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) {i : I}
    (j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) :
    Over.mk (Spec.map (c.ι.app i)) ⟶
      Over.mk (Spec.map (R.map (homOfLE j.val.property))) :=
  Over.homMk (Spec.map (c.ι.app j.val))
    (by dsimp; rw [← Spec.map_comp, c.w (homOfLE j.val.property)])

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Naturality transports a conjugated map through coherent object comparisons.
Source: naturality and inverse cancellation in Mathlib's category API.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
private theorem affineModel_conjugation
    {C D B : Type*} [Category C] [Category D] [Category B]
    (H : C ⥤ D) (G : C ⥤ B) (L : D ⥤ B) (δ : G ≅ H ⋙ L)
    {X Y : C} {U V : D} {Xk Yk U' V' : B}
    (κX : Xk ≅ G.obj X) (κY : Yk ≅ G.obj Y)
    (αX : H.obj X ≅ U) (αY : H.obj Y ≅ V)
    (γX : Xk ≅ U') (γY : Yk ≅ V')
    (εX : U' ≅ L.obj U) (εY : V' ≅ L.obj V)
    (hX : κX ≪≫ δ.app X ≪≫ L.mapIso αX ≪≫ εX.symm = γX)
    (hY : κY ≪≫ δ.app Y ≪≫ L.mapIso αY ≪≫ εY.symm = γY)
    (f : X ⟶ Y) :
    γX.inv ≫ κX.hom ≫ G.map f ≫ κY.inv ≫ γY.hom =
      εX.hom ≫ L.map (αX.inv ≫ H.map f ≫ αY.hom) ≫ εY.inv := by
  have hx := hX.symm
  have hy := hY.symm
  rw [hx, hy]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
    Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
  rw [δ.hom.naturality_assoc f]
  simp only [Iso.inv_hom_id_app_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Scalar extension of a map is conjugation by the explicit reassociation maps.
Source: Stacks Project, Tag 09RE; ModuleCat.extendScalarsComp.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
private theorem scalarExtensionHom_assoc
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (hc : h = g.comp f)
    (E K : CochainComplex (ModuleCat.{u} A) ℤ)
    (a : ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj E ⟶
      ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj K) :
    CochainComplex.scalarExtensionHom f g h hc E K a =
      (affineModelScalarAssocIso f g h hc E).hom ≫
        ((ModuleCat.extendScalars g).mapHomologicalComplex (.up ℤ)).map a ≫
          (affineModelScalarAssocIso f g h hc K).inv := by
  rw [affineModelScalarAssocIso_hom, affineModelScalarAssocIso_inv]
  dsimp only [CochainComplex.scalarExtensionHom]
  exact (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Apply naturality and inverse cancellation to scalar reassociation.
Source: Stacks, Tag 09RE, with Mathlib's naturality and scalar-extension APIs.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
private theorem affineModel_scalarConjugation
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (hc : h = g.comp f)
    (E K : CochainComplex (ModuleCat.{u} A) ℤ)
    {D T : Type*} [Category D] [Category T]
    (H : CochainComplex (ModuleCat.{u} B) ℤ ⥤ D)
    (G : CochainComplex (ModuleCat.{u} C) ℤ ⥤ T) (L : D ⥤ T)
    (δ : inducedFunctor (affineModelScalarPair f E K) ⋙
        (ModuleCat.extendScalars g).mapHomologicalComplex (.up ℤ) ⋙ G ≅
      inducedFunctor (affineModelScalarPair f E K) ⋙ H ⋙ L)
    {U V : D} {U' V' : T}
    (αE : H.obj (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj E) ≅ U)
    (αK : H.obj (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj K) ≅ V)
    (βE : G.obj (((ModuleCat.extendScalars h).mapHomologicalComplex (.up ℤ)).obj E) ≅ U')
    (βK : G.obj (((ModuleCat.extendScalars h).mapHomologicalComplex (.up ℤ)).obj K) ≅ V')
    (εE : U' ≅ L.obj U) (εK : V' ≅ L.obj V)
    (hE : G.mapIso (affineModelScalarAssocIso f g h hc E) ≪≫ δ.app true ≪≫
      L.mapIso αE ≪≫ εE.symm = βE)
    (hK : G.mapIso (affineModelScalarAssocIso f g h hc K) ≪≫ δ.app false ≪≫
      L.mapIso αK ≪≫ εK.symm = βK)
    (a : ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj E ⟶
      ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj K) :
    βE.inv ≫ G.map (CochainComplex.scalarExtensionHom f g h hc E K a) ≫ βK.hom =
      εE.hom ≫ L.map (αE.inv ≫ H.map a ≫ αK.hom) ≫ εK.inv := by
  have t := affineModel_conjugation
    (inducedFunctor (affineModelScalarPair f E K) ⋙ H)
    (inducedFunctor (affineModelScalarPair f E K) ⋙
      (ModuleCat.extendScalars g).mapHomologicalComplex (.up ℤ) ⋙ G)
    L δ (X := true) (Y := false)
    (G.mapIso (affineModelScalarAssocIso f g h hc E))
    (G.mapIso (affineModelScalarAssocIso f g h hc K))
    αE αK βE βK εE εK hE hK (InducedCategory.homMk (X := true) (Y := false) a)
  rw [scalarExtensionHom_assoc]
  simpa only [Functor.map_comp, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.comp_map, inducedFunctor_map, InducedCategory.homMk_hom,
    Category.assoc] using t

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The natural-isomorphism form of scalar conjugation avoids expanding its components.
Source: naturality and scalar reassociation; Stacks, Tag 09RE.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
theorem affineModel_scalarConjugation_nat
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (hc : h = g.comp f)
    (E K : CochainComplex (ModuleCat.{u} A) ℤ)
    {D T : Type*} [Category D] [Category T]
    (H : CochainComplex (ModuleCat.{u} B) ℤ ⥤ D)
    (G : CochainComplex (ModuleCat.{u} C) ℤ ⥤ T) (L : D ⥤ T)
    (δ : inducedFunctor (affineModelScalarPair f E K) ⋙
        (ModuleCat.extendScalars g).mapHomologicalComplex (.up ℤ) ⋙ G ≅
      inducedFunctor (affineModelScalarPair f E K) ⋙ H ⋙ L)
    {W : Type*} [Category W] (Ufun : W ⥤ D) (Vfun : W ⥤ T) (p q : W)
    (αE : H.obj (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj E) ≅ Ufun.obj p)
    (αK : H.obj (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj K) ≅ Ufun.obj q)
    (βE : G.obj (((ModuleCat.extendScalars h).mapHomologicalComplex (.up ℤ)).obj E) ≅ Vfun.obj p)
    (βK : G.obj (((ModuleCat.extendScalars h).mapHomologicalComplex (.up ℤ)).obj K) ≅ Vfun.obj q)
    (ε : Vfun ≅ Ufun ⋙ L)
    (hE : G.mapIso (affineModelScalarAssocIso f g h hc E) ≪≫ δ.app true ≪≫
      L.mapIso αE ≪≫ (ε.app p).symm = βE)
    (hK : G.mapIso (affineModelScalarAssocIso f g h hc K) ≪≫ δ.app false ≪≫
      L.mapIso αK ≪≫ (ε.app q).symm = βK)
    (a : ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj E ⟶
      ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj K) :
    βE.inv ≫ G.map (CochainComplex.scalarExtensionHom f g h hc E K a) ≫ βK.hom =
      ε.hom.app p ≫ L.map (αE.inv ≫ H.map a ≫ αK.hom) ≫ ε.inv.app q := by
  simpa only [Iso.app_hom, Iso.app_inv] using
    affineModel_scalarConjugation f g h hc E K H G L δ
      αE αK βE βK (ε.app p) (ε.app q) hE hK a


section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (Y : Scheme.{u}) [IsAffine Y] (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (P Q : schemeDerivedCategory Y)
    (F : Set.Ici i ⥤ CommRingCat.{u}) (C : Cocone F)
    (E K : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ)
    (d : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
          schemeDerivedCategory (Spec (F.obj j.val)) ≌
            schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE j.val.property)))))
      (dlim : schemeDerivedCategory (Spec (C.pt)) ≌
        schemeDerivedCategory (pullback s (Spec.map (c.ι.app i))))

/-- Object comparisons at every finite stage for one model.
Source: Stacks, Tag 09RE, affine model formula.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
abbrev AffineModelStageObjects : Type _ :=
  ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
    (affineModelLocalizedTilde (F.obj j.val) _ (d j)).obj
        ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj E) ≅
      (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.val.property))))).obj P

/-- Object comparison at the cocone point for one model.
Source: Stacks, Tag 09RE, affine model formula.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
abbrev AffineModelLimitObject : Type _ :=
  (affineModelLocalizedTilde C.pt _ dlim).obj
      (((ModuleCat.extendScalars (C.ι.app ⟨i, le_rfl⟩).hom).mapHomologicalComplex (.up ℤ)).obj E) ≅
    (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj P

/-- Natural affine comparisons for finite-stage arrows on the two labelled models.
Source: Stacks, Tags 09RE and 0D5S.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
abbrev AffineModelStageArrowComparisons : Type _ :=
  ∀ (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k),
    inducedFunctor (affineModelScalarPair (F.map (homOfLE j.property)).hom E K) ⋙
      (ModuleCat.extendScalars (F.map (homOfLE hjk)).hom).mapHomologicalComplex (.up ℤ) ⋙
        affineModelLocalizedTilde (F.obj k.val) _ (d k) ≅
    inducedFunctor (affineModelScalarPair (F.map (homOfLE j.property)).hom E K) ⋙
      affineModelLocalizedTilde (F.obj j.val) _ (d j) ⋙
        derivedPullback (baseChangeMap s (affineModelStageArrow R j k hjk))

/-- Natural affine comparisons for arrows to the cocone point on both labelled models.
Source: Stacks, Tags 09RE and 0D5S.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
abbrev AffineModelLimitArrowComparisons : Type _ :=
  ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
    inducedFunctor (affineModelScalarPair (F.map (homOfLE j.property)).hom E K) ⋙
      (ModuleCat.extendScalars (C.ι.app j.val).hom).mapHomologicalComplex (.up ℤ) ⋙
        affineModelLocalizedTilde C.pt _ dlim ≅
    inducedFunctor (affineModelScalarPair (F.map (homOfLE j.property)).hom E K) ⋙
      affineModelLocalizedTilde (F.obj j.val) _ (d j) ⋙
        derivedPullback (baseChangeMap s (affineModelLimitArrow R c j))

/-- The finite-stage object triangles, independently of conjugated chain maps.
Source: Stacks, Tags 09RE and 0D5S, composition comparisons.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
def affineModelStageObjectCoherence
    (αE : AffineModelStageObjects R i Y s P F E d)
    (αK : AffineModelStageObjects R i Y s Q F K d)
    (θ : AffineModelStageArrowComparisons R i Y s F E K d) : Prop :=
  ∀ (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k),
    let B := derivedPullback (baseChangeMap s (affineModelStageArrow R j k hjk))
    let ε := perfectHomComparison s (affineModelStageArrow R j k hjk)
    let hc := congrArg CommRingCat.Hom.hom
      (F.map_comp (homOfLE j.property) (homOfLE hjk))
    ((affineModelLocalizedTilde (F.obj k.val) _ (d k)).mapIso
        (affineModelScalarAssocIso (F.map (homOfLE j.property)).hom
          (F.map (homOfLE hjk)).hom (F.map (homOfLE k.property)).hom hc E) ≪≫
      (θ j k hjk).app true ≪≫ B.mapIso (αE j) ≪≫ (ε.app P).symm = αE k) ∧
    ((affineModelLocalizedTilde (F.obj k.val) _ (d k)).mapIso
        (affineModelScalarAssocIso (F.map (homOfLE j.property)).hom
          (F.map (homOfLE hjk)).hom (F.map (homOfLE k.property)).hom hc K) ≪≫
      (θ j k hjk).app false ≪≫ B.mapIso (αK j) ≪≫ (ε.app Q).symm = αK k)

/-- The cocone object triangles, independently of conjugated chain maps.
Source: Stacks, Tags 09RE and 0D5S, composition comparisons.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
def affineModelLimitObjectCoherence
    (αE : AffineModelStageObjects R i Y s P F E d)
    (αK : AffineModelStageObjects R i Y s Q F K d)
    (βE : AffineModelLimitObject R c i Y s P F C E dlim)
    (βK : AffineModelLimitObject R c i Y s Q F C K dlim)
    (θ : AffineModelLimitArrowComparisons R c i Y s F C E K d dlim) : Prop :=
  ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
    let B := derivedPullback (baseChangeMap s (affineModelLimitArrow R c j))
    let ε := perfectHomComparison s (affineModelLimitArrow R c j)
    let hc := congrArg CommRingCat.Hom.hom (C.w (homOfLE j.property)).symm
    ((affineModelLocalizedTilde C.pt _ dlim).mapIso
        (affineModelScalarAssocIso (F.map (homOfLE j.property)).hom
          (C.ι.app j.val).hom (C.ι.app ⟨i, le_rfl⟩).hom hc E) ≪≫
      (θ j).app true ≪≫ B.mapIso (αE j) ≪≫ (ε.app P).symm = βE) ∧
    ((affineModelLocalizedTilde C.pt _ dlim).mapIso
        (affineModelScalarAssocIso (F.map (homOfLE j.property)).hom
          (C.ι.app j.val).hom (C.ι.app ⟨i, le_rfl⟩).hom hc K) ≪≫
      (θ j).app false ≪≫ B.mapIso (αK j) ≪≫ (ε.app Q).symm = βK)

/-- Coherent comparison objects and their naturality data, stored without choosing a witness.
Source: Stacks Project, Tags 09RE and 0D5S.
(blueprint: lem-pc-affine-model-coherent-object-comparisons). -/
structure AffineModelCoherentObjects where
  αE : AffineModelStageObjects R i Y s P F E d
  αK : AffineModelStageObjects R i Y s Q F K d
  βE : AffineModelLimitObject R c i Y s P F C E dlim
  βK : AffineModelLimitObject R c i Y s Q F C K dlim
  θ : AffineModelStageArrowComparisons R i Y s F E K d
  θlim : AffineModelLimitArrowComparisons R c i Y s F C E K d dlim
  hstage : affineModelStageObjectCoherence R i Y s P Q F E K d αE αK θ
  hlim : affineModelLimitObjectCoherence R c i Y s P Q F C E K d dlim
    αE αK βE βK θlim

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Construct coherent object comparisons for the supplied stages and cocone point.
Source: Stacks Project, Tag 09RE (affine calculation), Tags 06Y1 and 0D5S.
(blueprint: lem-pc-affine-model-coherent-object-comparisons).

Proof: Extend E and K from the bottom to each j, preserving their acyclic-tensor
K-flatness by Tag 06Y1. For j→k apply the natural affine derived-pullback comparison
to the full two-label induced category on E(j),K(j). Conjugate with hd(j),hd(k),
using htrans.1 to identify the scheme arrow; this gives θ(j,k). The same construction
with hdlim and htrans.2 gives θlim(j). These natural isomorphisms include all maps
between the labelled objects, even when the two models coincide.
At the bottom, F.map_id and the tensor unitor identify identity scalar extension
with the original model. Apply the bottom-to-j affine comparison to E,K; pull back
aE,aK and compose with
the inverse of perfectHomComparison to obtain αE(j),αK(j). For the bottom-to-limit
arrow use the same construction to obtain βE,βK. In each triangle bottom→j→k or
bottom→j→limit, the underived tensor reassociation agrees with the counit-pinned
derived composition comparison, by its defining counit equation and associativity.
The ring equality is F.map_comp or C.w. Reassociation of module complexes is the
explicit affineModelScalarAssocIso. Transport this identity through hd and aE,aK;
it gives the four object-coherence equations below. Naturality cancellation for an
arbitrary chain map is a separate proved argument, not part of this statement.
Identity arrows, zero complexes, coincident labels, zero rings and empty spectra
use the same comparison; no directedness, colimit or boundedness is assumed. -/
theorem exists_affineModelCoherentObjectComparisons
    {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (Y : Scheme.{u}) [IsAffine Y] (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (P Q : schemeDerivedCategory Y)
    (F : Set.Ici i ⥤ CommRingCat.{u}) (C : Cocone F)
    (E K : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ)
    (hE : ∀ L : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ,
      L.Acyclic →
        (CochainComplex.mapBifunctor L E
          (MonoidalCategory.curriedTensor (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)))).Acyclic)
    (hK : ∀ L : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ,
      L.Acyclic →
        (CochainComplex.mapBifunctor L K
          (MonoidalCategory.curriedTensor (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)))).Acyclic)
    (σ : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
      Spec (F.obj j.val) ≅ pullback s (Spec.map (R.map (homOfLE j.val.property))))
    (τ : Spec C.pt ≅ pullback s (Spec.map (c.ι.app i)))
    (htrans :
      (∀ (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k),
        (σ k).hom ≫ baseChangeMap s
          (T := Over.mk (Spec.map (R.map (homOfLE j.val.property))))
          (T' := Over.mk (Spec.map (R.map (homOfLE k.val.property))))
          (Over.homMk (Spec.map (R.map (homOfLE hjk)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)) =
          Spec.map (F.map (homOfLE hjk)) ≫ (σ j).hom) ∧
      (∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
        τ.hom ≫ baseChangeMap s
          (T := Over.mk (Spec.map (R.map (homOfLE j.val.property))))
          (T' := Over.mk (Spec.map (c.ι.app i)))
          (Over.homMk (Spec.map (c.ι.app j.val))
            (by dsimp; rw [← Spec.map_comp, c.w (homOfLE j.val.property)])) =
          Spec.map (C.ι.app j.val) ≫ (σ j).hom))
    (d : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
          schemeDerivedCategory (Spec (F.obj j.val)) ≌
            schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE j.val.property)))))
      (dlim : schemeDerivedCategory (Spec (C.pt)) ≌
        schemeDerivedCategory (pullback s (Spec.map (c.ι.app i))))
    (hd : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
      DerivedCategory.Q ⋙ (d j).functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings (Spec (F.obj j.val)).toRingedSpace))
        (SheafOfModules.{u}
          (moduleRings (pullback s (Spec.map (R.map (homOfLE j.val.property)))).toRingedSpace))
        _ _ _ _
        (SheafOfModules.pushforward (σ j).hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
    (hdlim : DerivedCategory.Q ⋙ dlim.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings (Spec C.pt).toRingedSpace))
        (SheafOfModules.{u} (moduleRings (pullback s (Spec.map (c.ι.app i))).toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward τ.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
    (aE : (d ⟨⟨i, le_rfl⟩, le_rfl⟩).functor.obj
      (DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩))
        (SheafOfModules.{u} (moduleRings (Spec (F.obj ⟨i, le_rfl⟩)).toRingedSpace))
        _ _ _ _ (@id (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩) ⥤
          SheafOfModules.{u} (moduleRings (Spec (F.obj ⟨i, le_rfl⟩)).toRingedSpace))
          (tilde.functor (F.obj ⟨i, le_rfl⟩)))
        ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj E)) ≅
      (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE (le_refl i)))))).obj P)
    (aK : (d ⟨⟨i, le_rfl⟩, le_rfl⟩).functor.obj
      (DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩))
        (SheafOfModules.{u} (moduleRings (Spec (F.obj ⟨i, le_rfl⟩)).toRingedSpace))
        _ _ _ _ (@id (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩) ⥤
          SheafOfModules.{u} (moduleRings (Spec (F.obj ⟨i, le_rfl⟩)).toRingedSpace))
          (tilde.functor (F.obj ⟨i, le_rfl⟩)))
        ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj K)) ≅
      (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE (le_refl i)))))).obj Q) :
    Nonempty (AffineModelCoherentObjects R c i Y s P Q F C E K d dlim) := by sorry

end AlgebraicGeometry
```

### Original snapshot: `lean/Sheaf/AlgebraicGeometry/AffineModelComparisonData.lean`

SHA-256: `98376a6accc2d4dfaf26fa4b73040dca912517629a258761feb58e45a64369c2`

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectHomTransport
public import Sheaf.Algebra.Homology.ScalarExtensionHom
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Coherent comparison data for affine complex models
Source: Stacks Project, Tags 09RE and 08DW, affine comparison formula.
(blueprint: def-pc-affine-model-comparison-data). -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The explicit proposition of coherent scheme transports and model isomorphisms.
Its data are the derived equivalences, the four families of object isomorphisms,
and the two sheafified-chain-map compatibility equations written below. This is
notation for that formula, not data chosen from an existence theorem.
Source: Stacks Project, Tags 09RE and 08DW, affine comparison formula.
(blueprint: def-pc-affine-model-comparison-data). -/
@[irreducible]
def affineModelComparisonData
    {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (Y : Scheme.{u}) [IsAffine Y] (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (P Q : schemeDerivedCategory Y)
    (F : Set.Ici i ⥤ CommRingCat.{u}) (C : Cocone F)
    (E K : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ)
    : Prop :=
    let T (A : CommRingCat.{u}) :=
      @Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
        (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace))
        _ _ _ _ (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace)) (tilde.functor A))
        ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)
    ∃ (d : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
          schemeDerivedCategory (Spec (F.obj j.val)) ≌
            schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE j.val.property)))))
      (dlim : schemeDerivedCategory (Spec (C.pt)) ≌
        schemeDerivedCategory (pullback s (Spec.map (c.ι.app i))))
      (αE : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
          (d j).functor.obj (DerivedCategory.Q.obj
            ((T (F.obj j.val)).obj ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj E))) ≅
          (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.val.property))))).obj P)
      (αK : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
          (d j).functor.obj (DerivedCategory.Q.obj
            ((T (F.obj j.val)).obj ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj K))) ≅
          (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.val.property))))).obj Q)
      (βE : dlim.functor.obj (DerivedCategory.Q.obj
            ((T (C.pt : CommRingCat.{u})).obj ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (C.ι.app ⟨i, le_rfl⟩).hom) (.up ℤ)).obj E))) ≅
          (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj P)
      (βK : dlim.functor.obj (DerivedCategory.Q.obj
            ((T (C.pt : CommRingCat.{u})).obj ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (C.ι.app ⟨i, le_rfl⟩).hom) (.up ℤ)).obj K))) ≅
          (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj Q),
      (∀ (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k)
          (f : ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj E) ⟶
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj K)),
        (αE k).inv ≫ (d k).functor.map (DerivedCategory.Q.map
              ((T (F.obj k.val)).map (CochainComplex.scalarExtensionHom
                (F.map (homOfLE j.property)).hom (F.map (homOfLE hjk)).hom
                (F.map (homOfLE k.property)).hom
                (congrArg CommRingCat.Hom.hom (F.map_comp
                  (homOfLE j.property) (homOfLE hjk))) E K f))) ≫ (αK k).hom =
          perfectStageMap R s j.val.property hjk
            ((αE j).inv ≫ (d j).functor.map (DerivedCategory.Q.map
              ((T (F.obj j.val)).map (f))) ≫ (αK j).hom)) ∧
      (∀ (j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i))
          (f : ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj E) ⟶
            ((Functor.mapHomologicalComplex
              (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ)).obj K)),
        βE.inv ≫ dlim.functor.map (DerivedCategory.Q.map
              ((T (C.pt : CommRingCat.{u})).map (CochainComplex.scalarExtensionHom
                (F.map (homOfLE j.property)).hom (C.ι.app j.val).hom
                (C.ι.app ⟨i, le_rfl⟩).hom
                (congrArg CommRingCat.Hom.hom (C.w (homOfLE j.property)).symm)
                E K f))) ≫ βK.hom =
          perfectLimitMap R c s j.val.property
            ((αE j).inv ≫ (d j).functor.map (DerivedCategory.Q.map
              ((T (F.obj j.val)).map (f))) ≫ (αK j).hom))

end AlgebraicGeometry
```

### Original snapshot: `lean/Sheaf/AlgebraicGeometry/AffineModelComparisonDataFromHomEquations.lean`

SHA-256: `c5b3c16ad2d2125681a2768032dbd7df061b474c9a180764d4ba41d733bd5540`

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.AlgebraicGeometry.AffineModelComparisonData
public import Sheaf.AlgebraicGeometry.AffineModelCoherentObjectComparisons

/-! # Constructor interface for affine comparison data
Source: the explicit comparison-data formula, Stacks Project, Tag 09RE.
(blueprint: lem-pc-affine-model-comparison-data-from-hom-equations). -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Constructor API for the original comparison predicate, with canonical functor maps.
Source: the explicit defining formula of affineModelComparisonData.
(blueprint: lem-pc-affine-model-comparison-data-from-hom-equations).

Proof: Expand the explicit proposition affineModelComparisonData. Use the supplied
coordinate equivalences d and dlim and the supplied object comparisons as its six
existential witnesses. The two remaining goals are precisely hstage and hlim:
the map equation for affineModelLocalizedTilde is d.functor.map applied to Q.map
of termwise tilde, and affineModelTildeComplex is the original explicit termwise
tilde functor. The scalarExtensionHom and perfectStageMap/perfectLimitMap terms
are the same after expanding the named stage and limit arrows.
Proof irrelevance identifies the generated preorder and HasPullback
proof constants with the direct instances. No mathematical choice or new geometric
assertion is needed. Identity arrows, zero models and zero rings are included. -/
theorem affineModelComparisonData_of_hom_equations
    {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (Y : Scheme.{u}) [IsAffine Y] (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (P Q : schemeDerivedCategory Y)
    (F : Set.Ici i ⥤ CommRingCat.{u}) (C : Cocone F)
    (E K : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ)
    (d : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
          schemeDerivedCategory (Spec (F.obj j.val)) ≌
            schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE j.val.property)))))
      (dlim : schemeDerivedCategory (Spec (C.pt)) ≌
        schemeDerivedCategory (pullback s (Spec.map (c.ι.app i))))
    (αE : AffineModelStageObjects R i Y s P F E d)
    (αK : AffineModelStageObjects R i Y s Q F K d)
    (βE : AffineModelLimitObject R c i Y s P F C E dlim)
    (βK : AffineModelLimitObject R c i Y s Q F C K dlim)
    (hstage : ∀ (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k)
      (a : ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ))).obj E ⟶
        ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ))).obj K),
      (αE k).inv ≫ (affineModelLocalizedTilde (F.obj k.val) _ (d k)).map
        (CochainComplex.scalarExtensionHom
          (F.map (homOfLE j.property)).hom (F.map (homOfLE hjk)).hom
          (F.map (homOfLE k.property)).hom
          (congrArg CommRingCat.Hom.hom (F.map_comp (homOfLE j.property) (homOfLE hjk)))
          E K a) ≫ (αK k).hom =
      perfectStageMap R s j.val.property hjk
        ((αE j).inv ≫ (affineModelLocalizedTilde (F.obj j.val) _ (d j)).map a ≫ (αK j).hom))
    (hlim : ∀ (j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i))
      (a : ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ))).obj E ⟶
        ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ))).obj K),
      βE.inv ≫ (affineModelLocalizedTilde C.pt _ dlim).map
        (CochainComplex.scalarExtensionHom
          (F.map (homOfLE j.property)).hom (C.ι.app j.val).hom
          (C.ι.app ⟨i, le_rfl⟩).hom
          (congrArg CommRingCat.Hom.hom (C.w (homOfLE j.property)).symm) E K a) ≫ βK.hom =
      perfectLimitMap R c s j.val.property
        ((αE j).inv ≫ (affineModelLocalizedTilde (F.obj j.val) _ (d j)).map a ≫ (αK j).hom)) :
    affineModelComparisonData R c i Y s P Q F C E K := by
  delta affineModelComparisonData
  refine ⟨d, dlim, αE, αK, βE, βK, ?_, ?_⟩
  · intro j k hjk a
    exact hstage j k hjk a
  · intro j a
    exact hlim j a

end AlgebraicGeometry
```

### Original snapshot: `lean/Sheaf/AlgebraicGeometry/AffineModelComparisonOfBottomModels.lean`

SHA-256: `892a313766a319f737010150335e578c3011f000909edf3752516b79e86c36a0`

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.AlgebraicGeometry.AffineModelComparisonData
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.AlgebraicGeometry.AffineModelStageHomEquationOfCoherentObjects
import Sheaf.AlgebraicGeometry.AffineModelLimitHomEquationOfCoherentObjects

/-! # Propagation of bottom-stage affine models
Source: Stacks Project, Tags 09RE and 0D5S.
(blueprint: lem-pc-affine-model-comparison-of-bottom-models). -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Propagate two bottom-stage models through compatible affine coordinates.
Source: Stacks Project, Tag 09RE, affine calculation, and Tags 0D5S and 06Y1.
(blueprint: lem-pc-affine-model-comparison-of-bottom-models).

Proof: hE and hK are the acyclic-tensor K-flat criterion. For each stage j
pull aE and aK back along the bottom-to-j
base-change arrow, and compose with perfectHomComparison. Compute this
pullback on E and K by the K-flat affine pullback comparison, conjugated by
the localized pushforwards hd at the bottom and at j. The transition equation
for σ identifies the affine map with that base-change arrow. At the limit use
the same construction with hdlim and the limit transition equation. Extension
of scalars preserves K-flatness, so this calculation applies again to every
stage model. For a chain map at j, use naturality of the affine comparison for
the map j→k, respectively j→C.pt. Reassociation of scalar extension is exactly
the two associativity components in scalarExtensionHom. The counit
characterization of the derived composition comparisons, and its associativity
law, identify these reassociations with perfectHomComparison. Expand the
conjugations and cancel each adjacent inverse pair; this gives both Hom
equations in affineModelComparisonData. Package the supplied d and dlim and
the four constructed isomorphisms. The bottom isomorphisms are arbitrary:
their pullbacks appear on both sides of every naturality square and cancel.
No chain map is required to descend to the bottom, and no directedness or
colimit hypothesis is used. Identity arrows, zero rings, empty spectra and
zero models are covered by the same naturality and composition calculations. -/
theorem affineModelComparisonData_of_bottom_models
    {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (Y : Scheme.{u}) [IsAffine Y] (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (P Q : schemeDerivedCategory Y)
    (F : Set.Ici i ⥤ CommRingCat.{u}) (C : Cocone F)
    (E K : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ)
    (hE : ∀ L : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ,
      L.Acyclic →
        (CochainComplex.mapBifunctor L E
          (MonoidalCategory.curriedTensor (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)))).Acyclic)
    (hK : ∀ L : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ,
      L.Acyclic →
        (CochainComplex.mapBifunctor L K
          (MonoidalCategory.curriedTensor (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)))).Acyclic)
    (σ : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
      Spec (F.obj j.val) ≅ pullback s (Spec.map (R.map (homOfLE j.val.property))))
    (τ : Spec C.pt ≅ pullback s (Spec.map (c.ι.app i)))
    (htrans :
      (∀ (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k),
        (σ k).hom ≫ baseChangeMap s
          (T := Over.mk (Spec.map (R.map (homOfLE j.val.property))))
          (T' := Over.mk (Spec.map (R.map (homOfLE k.val.property))))
          (Over.homMk (Spec.map (R.map (homOfLE hjk)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)) =
          Spec.map (F.map (homOfLE hjk)) ≫ (σ j).hom) ∧
      (∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
        τ.hom ≫ baseChangeMap s
          (T := Over.mk (Spec.map (R.map (homOfLE j.val.property))))
          (T' := Over.mk (Spec.map (c.ι.app i)))
          (Over.homMk (Spec.map (c.ι.app j.val))
            (by dsimp; rw [← Spec.map_comp, c.w (homOfLE j.val.property)])) =
          Spec.map (C.ι.app j.val) ≫ (σ j).hom))
    (d : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
          schemeDerivedCategory (Spec (F.obj j.val)) ≌
            schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE j.val.property)))))
      (dlim : schemeDerivedCategory (Spec (C.pt)) ≌
        schemeDerivedCategory (pullback s (Spec.map (c.ι.app i))))
    (hd : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
      DerivedCategory.Q ⋙ (d j).functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings (Spec (F.obj j.val)).toRingedSpace))
        (SheafOfModules.{u}
          (moduleRings (pullback s (Spec.map (R.map (homOfLE j.val.property)))).toRingedSpace))
        _ _ _ _
        (SheafOfModules.pushforward (σ j).hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
    (hdlim : DerivedCategory.Q ⋙ dlim.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings (Spec C.pt).toRingedSpace))
        (SheafOfModules.{u} (moduleRings (pullback s (Spec.map (c.ι.app i))).toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward τ.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
    (aE : (d ⟨⟨i, le_rfl⟩, le_rfl⟩).functor.obj
      (DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩))
        (SheafOfModules.{u} (moduleRings (Spec (F.obj ⟨i, le_rfl⟩)).toRingedSpace))
        _ _ _ _ (@id (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩) ⥤
          SheafOfModules.{u} (moduleRings (Spec (F.obj ⟨i, le_rfl⟩)).toRingedSpace))
          (tilde.functor (F.obj ⟨i, le_rfl⟩)))
        ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj E)) ≅
      (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE (le_refl i)))))).obj P)
    (aK : (d ⟨⟨i, le_rfl⟩, le_rfl⟩).functor.obj
      (DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩))
        (SheafOfModules.{u} (moduleRings (Spec (F.obj ⟨i, le_rfl⟩)).toRingedSpace))
        _ _ _ _ (@id (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩) ⥤
          SheafOfModules.{u} (moduleRings (Spec (F.obj ⟨i, le_rfl⟩)).toRingedSpace))
          (tilde.functor (F.obj ⟨i, le_rfl⟩)))
        ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj K)) ≅
      (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE (le_refl i)))))).obj Q) :
    affineModelComparisonData R c i Y s P Q F C E K := by
  rename_i hD
  obtain ⟨m⟩ := @exists_affineModelCoherentObjectComparisons
    I _ R c i Y _ s hD P Q F C E K hE hK σ τ htrans d dlim hd hdlim aE aK
  apply affineModelComparisonData_of_hom_equations R c i Y s P Q F C E K d dlim
    m.αE m.αK m.βE m.βK
  · exact affineModelStageHomEquation_of_coherent_objects
      R c i Y s P Q F C E K d dlim m
  · exact affineModelLimitHomEquation_of_coherent_objects
      R c i Y s P Q F C E K d dlim m

end AlgebraicGeometry
```

### Original snapshot: `lean/Sheaf/AlgebraicGeometry/AffineModelLimitHomEquationOfCoherentObjects.lean`

SHA-256: `d68851fd9f6f12ee3db6cdf2640810a6bed1258859bda9e537af9d9f8c1e910e`

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.AlgebraicGeometry.AffineModelComparisonDataFromHomEquations

/-! # Hom transport from coherent affine object comparisons
Source: Stacks Project, Tags 09RE and 0D5S. -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The limit Hom equation follows from the natural comparison and object triangles.
Source: Stacks Project, Tag 09RE and derived pullback composition, Tag 0D5S.
(blueprint: lem-pc-affine-model-limit-hom-equation-of-coherent-objects).

Proof: Fix the arrow from j to the cocone point.
Apply naturality of the supplied full two-label comparison θ to the given chain
map a; it need not descend to the bottom. Scalar reassociation identifies
scalarExtensionHom with κE.hom followed by extension of a followed by κK.inv,
where κ is affineModelScalarAssocIso. The two object triangles express the
comparison at the target as κ, θ, pullback of the source comparison and the
inverse perfectHomComparison. Substitute these formulas and expand map_comp.
Cancel adjacent inverse pairs, use naturality of θ, then cancel its inverse
pair. The result is exactly the conjugated Hom transport written below.
Proof irrelevance identifies the generated pullback-instance proofs with the
named arrow representation. The argument includes identity arrows, zero rings,
zero complexes and coincident labelled objects. -/
theorem affineModelLimitHomEquation_of_coherent_objects
    {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (Y : Scheme.{u}) [IsAffine Y] (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (P Q : schemeDerivedCategory Y)
    (F : Set.Ici i ⥤ CommRingCat.{u}) (C : Cocone F)
    (E K : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ)
    (d : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
          schemeDerivedCategory (Spec (F.obj j.val)) ≌
            schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE j.val.property)))))
      (dlim : schemeDerivedCategory (Spec (C.pt)) ≌
        schemeDerivedCategory (pullback s (Spec.map (c.ι.app i))))
    (m : AffineModelCoherentObjects R c i Y s P Q F C E K d dlim) :
    ∀ (j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i))
      (a : ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ))).obj E ⟶
        ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ))).obj K),
      m.βE.inv ≫ (affineModelLocalizedTilde C.pt _ dlim).map
        (CochainComplex.scalarExtensionHom
          (F.map (homOfLE j.property)).hom (C.ι.app j.val).hom
          (C.ι.app ⟨i, le_rfl⟩).hom
          (congrArg CommRingCat.Hom.hom (C.w (homOfLE j.property)).symm) E K a) ≫ m.βK.hom =
      perfectLimitMap R c s j.val.property
        ((m.αE j).inv ≫
          (affineModelLocalizedTilde (F.obj j.val) _ (d j)).map a ≫ (m.αK j).hom) := by
  intro j a
  change _ = perfectHomMap s (affineModelLimitArrow R c j) _
  rw [perfectHomMap]
  have hE := (m.hlim j).1
  have hK := (m.hlim j).2
  generalize hε : perfectHomComparison s (affineModelLimitArrow R c j) = ε at hE hK ⊢
  exact affineModel_scalarConjugation_nat
    (F.map (homOfLE j.property)).hom (C.ι.app j.val).hom
    (C.ι.app ⟨i, le_rfl⟩).hom
    (congrArg CommRingCat.Hom.hom (C.w (homOfLE j.property)).symm) E K
    (affineModelLocalizedTilde (F.obj j.val) _ (d j))
    (affineModelLocalizedTilde C.pt _ dlim)
    (derivedPullback (baseChangeMap s (affineModelLimitArrow R c j)))
    (m.θlim j)
    (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE j.val.property)))))
    (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))) P Q
    (m.αE j) (m.αK j) m.βE m.βK ε hE hK a

end AlgebraicGeometry
```

### Original snapshot: `lean/Sheaf/AlgebraicGeometry/AffineModelStageHomEquationOfCoherentObjects.lean`

SHA-256: `d7f112260f28ebc0a376a780d7b8ea9a8a3a31ea827bbc70937ff69c3a1f0071`

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.AlgebraicGeometry.AffineModelComparisonDataFromHomEquations

/-! # Hom transport from coherent affine object comparisons
Source: Stacks Project, Tags 09RE and 0D5S. -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The stage Hom equation follows from the natural comparison and object triangles.
Source: Stacks Project, Tag 09RE and derived pullback composition, Tag 0D5S.
(blueprint: lem-pc-affine-model-stage-hom-equation-of-coherent-objects).

Proof: Fix the finite-stage arrow j→k.
Apply naturality of the supplied full two-label comparison θ to the given chain
map a; it need not descend to the bottom. Scalar reassociation identifies
scalarExtensionHom with κE.hom followed by extension of a followed by κK.inv,
where κ is affineModelScalarAssocIso. The two object triangles express the
comparison at the target as κ, θ, pullback of the source comparison and the
inverse perfectHomComparison. Substitute these formulas and expand map_comp.
Cancel adjacent inverse pairs, use naturality of θ, then cancel its inverse
pair. The result is exactly the conjugated Hom transport written below.
Proof irrelevance identifies the generated pullback-instance proofs with the
named arrow representation. The argument includes identity arrows, zero rings,
zero complexes and coincident labelled objects. -/
theorem affineModelStageHomEquation_of_coherent_objects
    {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (Y : Scheme.{u}) [IsAffine Y] (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (P Q : schemeDerivedCategory Y)
    (F : Set.Ici i ⥤ CommRingCat.{u}) (C : Cocone F)
    (E K : CochainComplex (ModuleCat.{u} (F.obj ⟨i, le_rfl⟩)) ℤ)
    (d : ∀ j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i),
          schemeDerivedCategory (Spec (F.obj j.val)) ≌
            schemeDerivedCategory (pullback s (Spec.map (R.map (homOfLE j.val.property)))))
      (dlim : schemeDerivedCategory (Spec (C.pt)) ≌
        schemeDerivedCategory (pullback s (Spec.map (c.ι.app i))))
    (m : AffineModelCoherentObjects R c i Y s P Q F C E K d dlim) :
    ∀ (j k : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) (hjk : j ≤ k)
      (a : ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ))).obj E ⟶
        ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (F.map (homOfLE j.property)).hom) (.up ℤ))).obj K),
      (m.αE k).inv ≫ (affineModelLocalizedTilde (F.obj k.val) _ (d k)).map
        (CochainComplex.scalarExtensionHom
          (F.map (homOfLE j.property)).hom (F.map (homOfLE hjk)).hom
          (F.map (homOfLE k.property)).hom
          (congrArg CommRingCat.Hom.hom (F.map_comp (homOfLE j.property) (homOfLE hjk)))
          E K a) ≫ (m.αK k).hom =
      perfectStageMap R s j.val.property hjk
        ((m.αE j).inv ≫
          (affineModelLocalizedTilde (F.obj j.val) _ (d j)).map a ≫ (m.αK j).hom) := by sorry

end AlgebraicGeometry
```

### Original snapshot: `lean/Sheaf/AlgebraicGeometry/DerivedCategory.lean`

SHA-256: `5be7ac9ea5544eebe24ab6bfd8a748deedbe78ccf8a33ea7e3f2d1c780db7240`

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # The derived category of sheaves of modules on a scheme

Source: literature/blueprint/master/blueprint/sec-picard-framework/
  sk-thm-picard-coherence/def-pc-derived-category.md, node def-pc-derived-category, order 643
(blueprint: def-pc-derived-category); Stacks Project, Derived Categories, Tag 05RU.

The O_X-modules are the shared carrier `SheafOfModules.{u} (moduleRings X.toRingedSpace)`
(the carrier of `RingedSpace.IsCoherent`, of derived restriction to opens and of the
ringed-space derived products; as a type it is `X.Modules`, but `X.Modules` carries its own
`Category` instance, so `HasDerivedCategory X.Modules` would be a second D(O_X)).
Its abelian structure is Mathlib's `SheafOfModules.instAbelian`; the localization is the
shared `[HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]` binder.

## Main definitions

* `schemeDerivedCategory` is the derived category `D(𝒪_X)` of sheaves of `𝒪_X`-modules.
* `schemeDerivedQCohProperty` says every cohomology sheaf is quasi-coherent.
* `schemeDerivedQCohCategory` is the full subcategory `D_QCoh(𝒪_X)`.
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry

/-- The derived category `D(𝒪_X)` of sheaves of `𝒪_X`-modules on a scheme `X`: Mathlib's
`DerivedCategory` (the localization of cochain complexes at quasi-isomorphisms, morphisms in
universe `w`) of the abelian category `SheafOfModules.{u} (moduleRings X.toRingedSpace)`.
Source: literature/blueprint/master/blueprint/sec-picard-framework/
  sk-thm-picard-coherence/def-pc-derived-category.md, node def-pc-derived-category
  (blueprint: def-pc-derived-category). -/
abbrev schemeDerivedCategory (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] : Type _ :=
  DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))

/-- An object `K` of `D(𝒪_X)` has quasi-coherent cohomology sheaves: for every `n : ℤ` the
cohomology sheaf `H^n(K)` is quasi-coherent (Mathlib's `SheafOfModules.IsQuasicoherent`).
Source: literature/blueprint/master/blueprint/sec-picard-framework/
  sk-thm-picard-coherence/def-pc-derived-category.md, node def-pc-derived-category
  (blueprint: def-pc-derived-category). -/
def schemeDerivedQCohProperty (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    ObjectProperty (schemeDerivedCategory X) :=
  fun K => ∀ n : ℤ,
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K).IsQuasicoherent

/-- The full subcategory `D_QCoh(𝒪_X)` of `D(𝒪_X)` of objects whose cohomology sheaves are
quasi-coherent.
Source: literature/blueprint/master/blueprint/sec-picard-framework/
  sk-thm-picard-coherence/def-pc-derived-category.md, node def-pc-derived-category
  (blueprint: def-pc-derived-category). -/
abbrev schemeDerivedQCohCategory (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] : Type _ :=
  (schemeDerivedQCohProperty X).FullSubcategory

end AlgebraicGeometry
```

### Original snapshot: `lean/Sheaf/AlgebraicGeometry/DerivedPullback.lean`

SHA-256: `a8f24c9daacd4779c737e340c2f5dd4c1f15a1114a771b0457484aee47a2f667`

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.AlgebraicGeometry.InverseImageExactKFlat
import Sheaf.AlgebraicGeometry.TensorPullbackKFlatQuasiIso
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Derived pullback of modules on schemes

Source: literature/blueprint/master/blueprint/sec-picard-framework/
  sk-thm-picard-semicon/def-pc-derived-pullback.md, node def-pc-derived-pullback
  (blueprint: def-pc-derived-pullback).

The derived pullback is the functor obtained by applying derived change of rings to
termwise inverse image along the morphism of schemes.  Its K-flat representatives
are the termwise tensor pullbacks of K-flat resolutions; the comparison maps are
canonical and independent of the chosen resolution.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

/-- Existence of the derived pullback functor associated with a morphism of schemes.

Source: literature/blueprint/master/blueprint/sec-picard-framework/
  sk-thm-picard-semicon/def-pc-derived-pullback.md, node def-pc-derived-pullback;
  the functor is `L g^* = L(g^sharp)^* ∘ g⁻¹`, and on a K-flat resolution
  `P ⟶ E` it is represented by `𝒪_T ⊗_{g⁻¹𝒪_S} g⁻¹P`.
The functor `I` is the exact module inverse image, and `E` is the recorded tensor
pullback, on the shared module-sheaf category instances. The universal property and
K-flat counit specify the derived composite uniquely up to canonical isomorphism.
Source: Stacks Project, Cohomology, Tags 06YI and 06YJ.
Proof (the three steps of the node):
1. The inverse-image stalk isomorphism (lem-weil-pbc-topological-inverse-image-stalk)
   and stalkwise exactness show that `I` is exact and preserves quasi-isomorphisms
   (def-pc-quasi-iso-modules), hence induces a functor on derived categories.
2. Apply lem-pur-derived-change-of-rings to `tensorPullbackRingMap g`. Compose its
   derived functor with derived inverse image. Termwise the composite is the recorded
   `tensorPullback g`; the resolving-class universal property gives the counit below.
3. Choose a K-flat resolution (lem-pc-kflat-resolution). Inverse image preserves its
   quasi-isomorphism by step 1 and its K-flatness by lem-pc-kflat-pullback-preservation
   applied to `(T, g⁻¹𝒪_S) → (S, 𝒪_S)`. The change-of-rings counit is therefore an
   isomorphism. The canonical comparison for `s : P → G` is the inverse of `L(Q(s))`
   followed by this counit at `P`. Comparisons between resolutions factor through
   `L(Q(G))`, so are independent of choices and compatible with composition.
(blueprint: def-pc-derived-pullback). -/
theorem exists_derivedPullback {T S : Scheme.{u}} (g : T ⟶ S)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))] :
    ∃ L : schemeDerivedCategory S ⥤ schemeDerivedCategory T,
      ∃ (I : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
          SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology T)
            (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (TopCat.Sheaf.inverseImageRing g.base S.sheaf)))
        (hI : ∀ M, I.obj M = TopCat.Sheaf.inverseImageModule g.base S.sheaf M)
        (_ : ∀ {M N} (a : M ⟶ N),
          I.map a = eqToHom (hI M) ≫
            TopCat.Sheaf.inverseImageModuleMap g.base S.sheaf M a ≫
              eqToHom (hI N).symm)
        (_ : I.Additive),
        PreservesFiniteLimits I ∧ PreservesFiniteColimits I ∧
        (∀ {P G : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ}
          (s : P ⟶ G), CochainComplex.IsKFlatResolution (R := S.sheaf) s →
            CochainComplex.IsKFlatResolution
              (R := TopCat.Sheaf.inverseImageRing g.base S.sheaf)
              ((I.mapHomologicalComplex (ComplexShape.up ℤ)).map s)) ∧
        ∃ (E : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
            SheafOfModules.{u} (moduleRings T.toRingedSpace))
          (h : ∀ M, E.obj M = Scheme.Modules.tensorPullbackObj g M)
          (_ : ∀ {M N} (a : M ⟶ N),
            E.map a = eqToHom (h M) ≫ Scheme.Modules.tensorPullbackMap g a ≫
              eqToHom (h N).symm)
          (_ : E.Additive)
          (ε : DerivedCategory.Qh ⋙ L ⟶
            E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
          L.IsLeftDerivedFunctor ε
              (HomotopyCategory.quasiIso
                (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (ComplexShape.up ℤ)) ∧
            (∃ (_ : L.CommShift ℤ), L.IsTriangulated) ∧
            ∀ P : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ,
              CochainComplex.IsKFlat (R := S.sheaf) P →
                IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := by
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres⟩ :=
    exists_inverseImage_exact_kFlat g
  let E : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings T.toRingedSpace) := Scheme.Modules.tensorPullback g
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction g
  let : E.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
  let : E.Additive := CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ E
    (by
      rw [CategoryTheory.rightExactFunctor_iff]
      infer_instance)
  let A := SheafOfModules.{u} (moduleRings S.toRingedSpace)
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let F := E.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  have : F.IsTriangulated := by
    dsimp only [F]
    set_option synthInstance.maxSize 512 in infer_instance
  let C : Set (HomotopyCategory A (ComplexShape.up ℤ)) :=
    {X | ∃ P : CochainComplex A ℤ,
      CochainComplex.IsKFlat (R := S.sheaf) P ∧ q.obj P = X}
  have hres : ∀ X : HomotopyCategory A (ComplexShape.up ℤ),
      ∃ (X' : HomotopyCategory A (ComplexShape.up ℤ)) (s : X' ⟶ X),
        X' ∈ C ∧ HomotopyCategory.quasiIso A (ComplexShape.up ℤ) s := by
    intro X
    obtain ⟨G, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨P, s, hP, _, hs, _⟩ := CochainComplex.exists_isKFlatResolution (R := S.sheaf) G
    refine ⟨q.obj P, q.map s, ⟨P, hP, rfl⟩, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs
  have hinv : ∀ (X X' : HomotopyCategory A (ComplexShape.up ℤ)) (s : X ⟶ X'),
      X ∈ C → X' ∈ C → HomotopyCategory.quasiIso A (ComplexShape.up ℤ) s →
        IsIso (F.map s) := by
    intro X X' s hX hX' hs
    obtain ⟨P, hP, rfl⟩ := hX
    obtain ⟨P', hP', rfl⟩ := hX'
    obtain ⟨s, rfl⟩ := q.map_surjective s
    have hsq : QuasiIso s := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).1 hs
    have ht := tensorPullback_quasiIso_of_isKFlat g s hP hP' hsq
    change IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map s)))
    exact Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 ht)
  obtain ⟨_, L, ε, hL, htri, hε⟩ :=
    CategoryTheory.Functor.leftDerived_from_resolvingClass A
      (schemeDerivedCategory T) F C hres hinv
  refine ⟨L, I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    E, (fun _ ↦ rfl), ?_, inferInstance, ε, hL, htri, ?_⟩
  · intro M N a
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · intro P hP
    exact hε (q.obj P) ⟨P, hP, rfl⟩

/-- The derived pullback `L g^* : D(𝒪_S) ⥤ D(𝒪_T)`.

For `g : T ⟶ S`, this is the composite of termwise inverse image and derived change
of rings along `g^sharp`.  If `P ⟶ E` is any K-flat resolution, its canonical
representative is `g^*P = 𝒪_T ⊗_{g⁻¹𝒪_S} g⁻¹P`; the comparison isomorphisms supplied
by derived change of rings make this independent of `P`.
Source: literature/blueprint/master/blueprint/sec-picard-framework/
  sk-thm-picard-semicon/def-pc-derived-pullback.md, node def-pc-derived-pullback
  (blueprint: def-pc-derived-pullback). -/
noncomputable def derivedPullback {T S : Scheme.{u}} (g : T ⟶ S)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))] :
    schemeDerivedCategory S ⥤ schemeDerivedCategory T :=
  Classical.choose (exists_derivedPullback g)

end AlgebraicGeometry
```

### Original snapshot: `lean/Sheaf/AlgebraicGeometry/DerivedPullbackComposition.lean`

SHA-256: `7fc9af4fe9a537138ac38511d0fae8666639828d20cb25c06718767fb839b1bd`

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import Sheaf.AlgebraicGeometry.DerivedPullbackCompositionIsIso
import Sheaf.AlgebraicGeometry.DerivedPullbackCompositionCoherence

/-!
# Composition and coherence of derived pullbacks

Source: Stacks Project, Cohomology, Lemma 20.27.2, Tag 0D5S
(blueprint: lem-pc-ringed-spaces-derived-pullback-composition).
-/

@[expose] public section

universe u₁ w₁

open CategoryTheory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

private theorem tensorDerivedCounit {X Y : Scheme.{u₁}} (f : X ⟶ Y)
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace))] :
    ∃ (_ : (Scheme.Modules.tensorPullback f).Additive)
      (ε : DerivedCategory.Qh ⋙ derivedPullback f ⟶
        (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh
            (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace))),
      (derivedPullback f).IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)) ∧
      ∀ P : CochainComplex (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace)) ℤ,
        CochainComplex.IsKFlat (R := Y.sheaf) P →
          IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := by
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    E, hE, hEmap, hEadd, ε, hL, htri, hK⟩ :=
      Classical.choose_spec (exists_derivedPullback f)
  have h : E = Scheme.Modules.tensorPullback f :=
    CategoryTheory.Functor.ext hE (fun M N a ↦ hEmap a)
  subst E
  exact ⟨hEadd, ε, hL, hK⟩

/-- The canonical composition comparisons `c f g : Lf^* ∘ Lg^* ≅ L(g ∘ f)^*` of derived
pullbacks, together with identity comparisons `i X : L(id_X)^* ≅ id`, both unit laws and
associativity. The comparison is tied to the left-derived universal property: `ε f` is a
left-derived counit of `derivedPullback f` for the recorded tensor pullback, and `c f g` is
the morphism into the left derived functor `derivedPullback (f ≫ g)` induced by the counits
of `g` and `f` followed by the canonical underived identification
`tensorPullback g ⋙ tensorPullback f ≅ tensorPullback (f ≫ g)`, the conjugate of
`pushforwardComp f g` under the pinned tensor-pullback adjunctions.
The family of derived-category instances only chooses the localizations; it imposes no
geometric condition on the schemes or morphisms.
Source: Stacks Project, Cohomology, Tag 0D5S
(blueprint: lem-pc-ringed-spaces-derived-pullback-composition).
Proof, step 1: choose a K-flat resolution on Z (lem-pc-kflat-resolution). Pullback
preserves K-flatness (lem-pc-kflat-pullback-preservation), so successive derived
pullbacks are represented by successive termwise tensor pullbacks (def-pc-derived-pullback):
the counits at a K-flat complex and at its pullback are invertible. The canonical underived
identification then makes the induced morphism into `L(g ∘ f)^*` invertible, natural in
the complex.
Step 2: identity pullback is the tensor unitor. On a K-flat representative the two
unit laws are the tensor unit laws, and the two triple-composition paths are the two
reassociations of the same tensor expression; tensor associativity makes them equal.
Uniqueness of morphisms into a left derived functor descends these laws to the derived
categories. -/
theorem exists_derivedPullbackComposition
    [d : ∀ X : Scheme.{u₁}, HasDerivedCategory.{w₁}
      (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))] :
    ∃ (_ : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y), (Scheme.Modules.tensorPullback f).Additive)
      (ε : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y),
        DerivedCategory.Qh ⋙ derivedPullback f ⟶
          (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))
      (_ : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y),
        (derivedPullback f).IsLeftDerivedFunctor (ε f)
          (HomotopyCategory.quasiIso
            (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))),
    ∃ c : ∀ {X Y Z : Scheme.{u₁}} (f : X ⟶ Y) (g : Y ⟶ Z),
        derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g),
      (∀ {X Y Z : Scheme.{u₁}} (f : X ⟶ Y) (g : Y ⟶ Z),
        (c f g).hom =
          (derivedPullback (f ≫ g)).leftDerivedLift (ε (f ≫ g))
            (HomotopyCategory.quasiIso
              (SheafOfModules.{u₁} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ))
            (derivedPullback g ⋙ derivedPullback f)
            ((Functor.associator DerivedCategory.Qh (derivedPullback g)
                (derivedPullback f)).inv ≫
              Functor.whiskerRight (ε g) (derivedPullback f) ≫
              (Functor.associator _ DerivedCategory.Qh (derivedPullback f)).hom ≫
              Functor.whiskerLeft _ (ε f) ≫
              (Functor.associator _ _
                (DerivedCategory.Qh (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))).inv ≫
              Functor.whiskerRight
                (Functor.mapHomotopyCategoryCompIso
                  ((conjugateIsoEquiv
                    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
                    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
                      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
                    (Scheme.Modules.pushforwardComp f g).symm)
                  (ComplexShape.up ℤ)).hom
                (DerivedCategory.Qh (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace))))) ∧
      ∃ i : ∀ X : Scheme.{u₁}, derivedPullback (𝟙 X) ≅ 𝟭 _,
        (∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y),
          c (𝟙 X) f ≪≫
            eqToIso (congrArg (fun k : X ⟶ Y => derivedPullback k) (Category.id_comp f)) =
            Functor.isoWhiskerLeft (derivedPullback f) (i X) ≪≫
              Functor.rightUnitor (derivedPullback f)) ∧
        (∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y),
          c f (𝟙 Y) ≪≫
            eqToIso (congrArg (fun k : X ⟶ Y => derivedPullback k) (Category.comp_id f)) =
            Functor.isoWhiskerRight (i Y) (derivedPullback f) ≪≫
              Functor.leftUnitor (derivedPullback f)) ∧
        (∀ {W X Y Z : Scheme.{u₁}} (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z),
          Functor.isoWhiskerRight (c f g) (derivedPullback h) ≪≫ c h (f ≫ g) =
            Functor.associator (derivedPullback g) (derivedPullback f)
                (derivedPullback h) ≪≫
              Functor.isoWhiskerLeft (derivedPullback g) (c h f) ≪≫ c (h ≫ f) g ≪≫
                eqToIso (congrArg (fun k : W ⟶ Z => derivedPullback k)
                  (Category.assoc h f g))) := by
  classical
  let a : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y),
      (Scheme.Modules.tensorPullback f).Additive := fun f ↦
    Classical.choose (tensorDerivedCounit f)
  let ε : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y),
      DerivedCategory.Qh ⋙ derivedPullback f ⟶
        (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)) :=
    fun f ↦ Classical.choose (Classical.choose_spec (tensorDerivedCounit f))
  have hL := fun {X Y : Scheme.{u₁}} (f : X ⟶ Y) ↦
    (Classical.choose_spec (Classical.choose_spec (tensorDerivedCounit f))).1
  have hK := fun {X Y : Scheme.{u₁}} (f : X ⟶ Y) ↦
    (Classical.choose_spec (Classical.choose_spec (tensorDerivedCounit f))).2
  let c : ∀ {X Y Z : Scheme.{u₁}} (f : X ⟶ Y) (g : Y ⟶ Z),
      derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g) := fun {X Y Z} f g ↦ by
    have := isIso_derivedPullbackCompositionLift a ε hL hK f g
    exact asIso ((derivedPullback (f ≫ g)).leftDerivedLift (ε (f ≫ g))
            (HomotopyCategory.quasiIso
              (SheafOfModules.{u₁} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ))
            (derivedPullback g ⋙ derivedPullback f)
            ((Functor.associator DerivedCategory.Qh (derivedPullback g)
                (derivedPullback f)).inv ≫
              Functor.whiskerRight (ε g) (derivedPullback f) ≫
              (Functor.associator _ DerivedCategory.Qh (derivedPullback f)).hom ≫
              Functor.whiskerLeft _ (ε f) ≫
              (Functor.associator _ _
                (DerivedCategory.Qh (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))).inv ≫
              Functor.whiskerRight
                (Functor.mapHomotopyCategoryCompIso
                  ((conjugateIsoEquiv
                    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
                    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
                      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
                    (Scheme.Modules.pushforwardComp f g).symm)
                  (ComplexShape.up ℤ)).hom
                (DerivedCategory.Qh
                (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))))
  refine ⟨a, ε, hL, c, ?_, ?_⟩
  · intro X Y Z f g
    rfl
  · exact derivedPullbackComposition_coherence a ε hL hK c (fun _ _ ↦ rfl)

end AlgebraicGeometry
```

### Original snapshot: `lean/Sheaf/AlgebraicGeometry/PerfectHomTransport.lean`

SHA-256: `fd3ba055926eb52b9afcd56ed8bfcebc883760badecb8d6deef058cacb6e8744`

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
public import WeilConjectures.AlgebraicGeometry.Picard.TwistedDescent

/-! # Canonical transport of Hom groups in the base-change system.
Source: Stacks Project, Cohomology, Tag 0D5S and perfect.tex, Tag 09RE.
(blueprint: lem-pc-perfect-hom-transport).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- The fixed counit-pinned comparison for composition of derived pullbacks.
Source: Stacks Project, Tag 0D5S (blueprint: lem-pc-perfect-hom-transport). -/
noncomputable def perfectHomComposition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition))) f g

/-- The counit-pinned comparison for a base-change arrow. This is the same fixed
construction as `perfectDescentComparison`, with no independently chosen data.
Source: Stacks Project, Tag 0D5S
(blueprint: lem-pc-perfect-hom-transport). -/
noncomputable def perfectHomComparison {X S : Scheme.{u}} (s : X ⟶ S)
    {T T' : Over S} (g : T' ⟶ T) :
    derivedPullback (pullback.fst s T'.hom) ≅
      derivedPullback (pullback.fst s T.hom) ⋙ derivedPullback (baseChangeMap s g) :=
  eqToIso (congrArg (fun k ↦ derivedPullback k) (baseChangeMap_fst s g).symm) ≪≫
    (perfectHomComposition (baseChangeMap s g) (pullback.fst s T.hom)).symm

/-- Conjugate pullback on Hom by the fixed composition comparisons.
Source: Stacks Project, Tag 09RE (blueprint: lem-pc-perfect-hom-transport). -/
noncomputable def perfectHomMap {X S : Scheme.{u}} (s : X ⟶ S)
    {T T' : Over S} (g : T' ⟶ T) {P Q : schemeDerivedCategory X}
    (f : (derivedPullback (pullback.fst s T.hom)).obj P ⟶
      (derivedPullback (pullback.fst s T.hom)).obj Q) :
    (derivedPullback (pullback.fst s T'.hom)).obj P ⟶
      (derivedPullback (pullback.fst s T'.hom)).obj Q :=
  (perfectHomComparison s g).hom.app P ≫
    (derivedPullback (baseChangeMap s g)).map f ≫ (perfectHomComparison s g).inv.app Q

@[simp] theorem perfectHomMap_id {X S : Scheme.{u}} (s : X ⟶ S)
    {T T' : Over S} (g : T' ⟶ T) (P : schemeDerivedCategory X) :
    perfectHomMap s g (𝟙 ((derivedPullback (pullback.fst s T.hom)).obj P)) =
      𝟙 _ := by
  simp [perfectHomMap]

@[simp] theorem perfectHomMap_comp {X S : Scheme.{u}} (s : X ⟶ S)
    {T T' : Over S} (g : T' ⟶ T) {P Q K : schemeDerivedCategory X}
    (a : (derivedPullback (pullback.fst s T.hom)).obj P ⟶
      (derivedPullback (pullback.fst s T.hom)).obj Q)
    (b : (derivedPullback (pullback.fst s T.hom)).obj Q ⟶
      (derivedPullback (pullback.fst s T.hom)).obj K) :
    perfectHomMap s g (a ≫ b) = perfectHomMap s g a ≫ perfectHomMap s g b := by
  simp [perfectHomMap, Category.assoc]

theorem perfectHomMap_eq_iff {X S : Scheme.{u}} (s : X ⟶ S)
    {T T' : Over S} (g : T' ⟶ T) {P Q : schemeDerivedCategory X}
    (a b : (derivedPullback (pullback.fst s T.hom)).obj P ⟶
      (derivedPullback (pullback.fst s T.hom)).obj Q) :
    perfectHomMap s g a = perfectHomMap s g b ↔
      (derivedPullback (baseChangeMap s g)).map a =
        (derivedPullback (baseChangeMap s g)).map b := by
  simp only [perfectHomMap, cancel_epi, cancel_mono]


private theorem cc_assoc {W X Y Z : Scheme.{u}} (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.isoWhiskerRight (perfectHomComposition f g) (derivedPullback h) ≪≫
      perfectHomComposition h (f ≫ g) =
      Functor.associator (derivedPullback g) (derivedPullback f) (derivedPullback h) ≪≫
        Functor.isoWhiskerLeft (derivedPullback g) (perfectHomComposition h f) ≪≫
          perfectHomComposition (h ≫ f) g ≪≫
          eqToIso (congrArg (fun k : W ⟶ Z ↦ derivedPullback k) (Category.assoc h f g)) := by
  exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec
      exists_derivedPullbackComposition)))).2).2.2 h f g

private noncomputable def tr {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {P Q : schemeDerivedCategory Z}
    (a : (derivedPullback g).obj P ⟶ (derivedPullback g).obj Q) :
    (derivedPullback (f ≫ g)).obj P ⟶ (derivedPullback (f ≫ g)).obj Q :=
  (perfectHomComposition f g).inv.app P ≫ (derivedPullback f).map a ≫
    (perfectHomComposition f g).hom.app Q

private theorem tr_assoc {W X Y Z : Scheme.{u}} (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z)
    {P Q : schemeDerivedCategory Z}
    (a : (derivedPullback g).obj P ⟶ (derivedPullback g).obj Q) :
    tr h (f ≫ g) (tr f g a) =
      (eqToIso (congrArg (fun k : W ⟶ Z ↦ derivedPullback k)
        (Category.assoc h f g))).inv.app P ≫ tr (h ≫ f) g a ≫
      (eqToIso (congrArg (fun k : W ⟶ Z ↦ derivedPullback k)
        (Category.assoc h f g))).hom.app Q := by
  have hi := congrArg (fun e ↦ e.inv.app P) (cc_assoc h f g)
  have hh := congrArg (fun e ↦ e.hom.app Q) (cc_assoc h f g)
  simp only [Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Category.comp_id, Category.id_comp, Category.assoc] at hi hh
  simp only [tr, Functor.map_comp]
  simp only [Category.assoc] at hi hh ⊢
  rw [← Category.assoc ((perfectHomComposition h (f ≫ g)).inv.app P)
    ((derivedPullback h).map ((perfectHomComposition f g).inv.app P)), hi]
  simp only [Category.assoc]
  rw [hh]
  have hn := (perfectHomComposition h f).hom.naturality a
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc ((derivedPullback h).map ((derivedPullback f).map a)), hn]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

private noncomputable def trTo {X Y Z : Scheme.{u}} (f : X ⟶ Y) (p : Y ⟶ Z)
    (q : X ⟶ Z) (e : f ≫ p = q) {P Q : schemeDerivedCategory Z}
    (a : (derivedPullback p).obj P ⟶ (derivedPullback p).obj Q) :
    (derivedPullback q).obj P ⟶ (derivedPullback q).obj Q :=
  (eqToIso (congrArg (fun k ↦ derivedPullback k) e.symm)).hom.app P ≫
    tr f p a ≫ (eqToIso (congrArg (fun k ↦ derivedPullback k) e.symm)).inv.app Q

private theorem trTo_refl {X Y Z : Scheme.{u}} (f : X ⟶ Y) (p : Y ⟶ Z)
    {P Q : schemeDerivedCategory Z}
    (a : (derivedPullback p).obj P ⟶ (derivedPullback p).obj Q) :
    trTo f p (f ≫ p) rfl a = tr f p a := by
  simp only [trTo, eqToIso_refl, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp, Category.comp_id]

set_option maxHeartbeats 800000 in
-- Comparing the fixed composition isomorphisms reduces their universal properties.
private theorem trTo_assoc {W X Y Z : Scheme.{u}} (h : W ⟶ X) (f : X ⟶ Y)
    (p : Y ⟶ Z) (q : X ⟶ Z) (r : W ⟶ Z) (eq : f ≫ p = q) (er : h ≫ q = r)
    {P Q : schemeDerivedCategory Z}
    (a : (derivedPullback p).obj P ⟶ (derivedPullback p).obj Q) :
    trTo h q r er (trTo f p q eq a) =
      trTo (h ≫ f) p r (by rw [Category.assoc, eq, er]) a := by
  subst q
  subst r
  rw [trTo_refl, trTo_refl]
  have he : eqToIso (congrArg (fun k : W ⟶ Z ↦ derivedPullback k)
      (Category.assoc h f p).symm) =
      (eqToIso (congrArg (fun k : W ⟶ Z ↦ derivedPullback k)
        (Category.assoc h f p))).symm := rfl
  conv_rhs => unfold trTo
  rw [he]
  exact tr_assoc h f p a

private theorem trTo_congr {X Y Z : Scheme.{u}} (f f' : X ⟶ Y) (p : Y ⟶ Z)
    (q : X ⟶ Z) (e : f ≫ p = q) (e' : f' ≫ p = q) (hf : f = f')
    {P Q : schemeDerivedCategory Z}
    (a : (derivedPullback p).obj P ⟶ (derivedPullback p).obj Q) :
    trTo f p q e a = trTo f' p q e' a := by
  subst f'
  rfl

private theorem homMap_trTo {X S : Scheme.{u}} (s : X ⟶ S) {T T' : Over S}
    (g : T' ⟶ T) {P Q : schemeDerivedCategory X}
    (a : (derivedPullback (pullback.fst s T.hom)).obj P ⟶
      (derivedPullback (pullback.fst s T.hom)).obj Q) :
    perfectHomMap s g a = trTo (baseChangeMap s g) (pullback.fst s T.hom)
      (pullback.fst s T'.hom) (baseChangeMap_fst s g) a := by
  simp only [trTo, tr, perfectHomMap, perfectHomComparison, Iso.trans_hom,
    Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Category.assoc]

set_option maxHeartbeats 800000 in
-- Reducing the fixed comparison construction exposes the conjugation formula.
/-- Conjugated Hom transport composes along successive base-change maps.
Source: Stacks Project, Tags 0D5S and 09RE
(blueprint: lem-pc-perfect-hom-transport). -/
theorem perfectHomMap_trans {X S : Scheme.{u}} (s : X ⟶ S) {T T' T'' : Over S}
    (g : T' ⟶ T) (h : T'' ⟶ T') {P Q : schemeDerivedCategory X}
    (a : (derivedPullback (pullback.fst s T.hom)).obj P ⟶
      (derivedPullback (pullback.fst s T.hom)).obj Q) :
    perfectHomMap s h (perfectHomMap s g a) = perfectHomMap s (h ≫ g) a := by
  have ht := trTo_assoc (baseChangeMap s h) (baseChangeMap s g)
    (pullback.fst s T.hom) (pullback.fst s T'.hom) (pullback.fst s T''.hom)
    (baseChangeMap_fst s g) (baseChangeMap_fst s h) a
  rw [homMap_trTo, homMap_trTo, homMap_trTo]
  apply ht.trans
  exact trTo_congr _ _ _ _ _ _ (baseChangeMap_comp s h g).symm a

/-- Transport from one finite stage to a later finite stage.
Source: Stacks Project, Tag 09RE (blueprint: lem-pc-perfect-hom-transport). -/
noncomputable def perfectStageMap {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u})
    {i : I} {X : Scheme.{u}} (s : X ⟶ Spec (R.obj i))
    {j k : I} (hij : i ≤ j) (hjk : j ≤ k)
    {P Q : schemeDerivedCategory X}
    (f : (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj P ⟶
      (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj Q) :=
  perfectHomMap s
    (T := Over.mk (Spec.map (R.map (homOfLE hij))))
    (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
    (Over.homMk (Spec.map (R.map (homOfLE hjk)))
      (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)) f

/-- Transport from a finite stage to the colimit scheme.
Source: Stacks Project, Tag 09RE (blueprint: lem-pc-perfect-hom-transport). -/
noncomputable def perfectLimitMap {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u})
    (c : Cocone R) {i : I} {X : Scheme.{u}} (s : X ⟶ Spec (R.obj i))
    {j : I} (hij : i ≤ j) {P Q : schemeDerivedCategory X}
    (f : (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj P ⟶
      (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj Q) :=
  perfectHomMap s
    (T := Over.mk (Spec.map (R.map (homOfLE hij))))
    (T' := Over.mk (Spec.map (c.ι.app i)))
    (Over.homMk (Spec.map (c.ι.app j))
      (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])) f

@[simp] theorem perfectStageMap_id {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) {i : I} {X : Scheme.{u}} (s : X ⟶ Spec (R.obj i))
    {j k : I} (hij : i ≤ j) (hjk : j ≤ k) (P : schemeDerivedCategory X) :
    perfectStageMap R s hij hjk
      (𝟙 ((derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj P)) =
        𝟙 _ := by
  exact perfectHomMap_id s
    (T := Over.mk (Spec.map (R.map (homOfLE hij))))
    (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
    (Over.homMk (Spec.map (R.map (homOfLE hjk)))
      (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)) P

@[simp] theorem perfectLimitMap_id {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) {i : I} {X : Scheme.{u}}
    (s : X ⟶ Spec (R.obj i)) {j : I} (hij : i ≤ j) (P : schemeDerivedCategory X) :
    perfectLimitMap R c s hij
      (𝟙 ((derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj P)) =
        𝟙 _ := by
  exact perfectHomMap_id s
    (T := Over.mk (Spec.map (R.map (homOfLE hij))))
    (T' := Over.mk (Spec.map (c.ι.app i)))
    (Over.homMk (Spec.map (c.ι.app j))
      (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])) P

/-- Transport to the colimit is compatible with increasing the finite stage.
No perfectness or finite-presentation hypothesis is needed for this coherence identity.
Source: Stacks Project, Cohomology, Tag 0D5S, and perfect.tex, Tag 09RE
(blueprint: lem-pc-perfect-hom-transport).

Proof: apply the associativity law of `exists_derivedPullbackComposition` to the
finite-stage base-change map, the map from the colimit scheme, and the projection
onto X. The equality of their composite base-change map with the direct map follows
from the pullback universal property and the cocone equation. Whisker the resulting
comparison identity at P and Q; naturality of the composition comparison transports
pullback of f. Cancel the adjacent comparison and inverse-comparison components.
The resulting conjugated Hom maps are precisely the two sides below. -/
theorem perfectLimitMap_stage {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u})
    (c : Cocone R) {i : I} {X : Scheme.{u}} (s : X ⟶ Spec (R.obj i))
    {j k : I} (hij : i ≤ j) (hjk : j ≤ k) {P Q : schemeDerivedCategory X}
    (f : (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj P ⟶
      (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj Q) :
    perfectLimitMap R c s (hij.trans hjk) (perfectStageMap R s hij hjk f) =
      perfectLimitMap R c s hij f := by
  unfold perfectLimitMap perfectStageMap
  rw [perfectHomMap_trans]
  congr 1
  ext
  change Spec.map (c.ι.app k) ≫ Spec.map (R.map (homOfLE hjk)) = Spec.map (c.ι.app j)
  rw [← Spec.map_comp, c.w (homOfLE hjk)]

end AlgebraicGeometry
```
