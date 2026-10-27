## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceAffineFinitePresentationLimit` states
`AlgebraicGeometry.AlgebraicSpace.exists_affine_finitePresentation_limit` with its proof
exactly `sorry`. There are no new definitions, dependency repairs or statement corrections.
Source read: `literature/stacks-project/spaces-limits.tex`, lemma-affine-morphism-is-limit,
Tag 0870, including the proof by finitely presented quasi-coherent algebra approximation.
The accepted DAG proof's three steps are included in the theorem docstring.

Clause-by-clause correspondence:

- A scheme S and spaces Z,B over S: `{S : Scheme.{u}} {Z B : AlgebraicSpace S}`.
  The recorded category is the full subcategory of `Sheaf (Scheme.fppfTopology.over S)
  (Type u)` cut out by `IsAlgebraicSpace`; its morphisms are natural transformations.
- The specified map p is `(p : Z ⟶ B)`.
- Affineness is `hp : MapIsAffine p`. The shared predicate supplies an affine
  representing scheme and a cartesian square after every affine scheme test, exactly
  the node's affine-test formulation. It does not require Z or B to be schemes.
- Quasi-compactness of B is exactly the specified atlas definition:
  `hqc : IsQuasiCompact B.obj`. Its shared definition is precisely
  `∃ (U : Over S) (a : yoneda.obj U ⟶ B.obj.obj),
  CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a`.
- Absolute quasi-separatedness of B is `hqs : IsAbsolutelyQuasiSeparated B`. Its shared
  definition is the affine-pair criterion of Stacks 0AHR(3), equivalent to quasi-compactness
  of the absolute diagonal. It imposes no quasi-separatedness on S and does not replace
  absolute quasi-separatedness by that of B/S.
- A small nonempty directed set: existential `I : Type u`, `Preorder I`, `Nonempty I`,
  `IsDirected I (· ≤ ·)`. This uses the same small universe as the schemes. A preorder
  is the project's directed-set convention (Stacks 00D3); no linear order is required.
- Inverse system over B: `D : Iᵒᵖ ⥤ Over B`. The functor supplies identity and composition
  laws, and the slice supplies the structure maps and transition equations over B.
- Compatible B-maps from Z: `π : (Functor.const Iᵒᵖ).obj (Over.mk p) ⟶ D`. Each component
  is a slice morphism, and naturality is exactly compatibility with every transition.
- Each stage is affine: the first conjunct for each i is `MapIsAffine (D.obj i).hom`.
- Each stage is finitely presented: the next three conjuncts are
  `IsQuasiCompactPresheafMap (D.obj i).hom.hom.hom`, the same predicate on
  `pullback.diagonal (D.obj i).hom.hom.hom`, and
  `MapIsLocallyOfFinitePresentation (D.obj i).hom`. The first predicate uses a
  quasi-compact scheme surjective etale atlas on every affine scheme pullback, exactly
  the node's quasi-compactness convention. Its diagonal version is relative
  quasi-separatedness; the final predicate tests scheme `LocallyOfFinitePresentation`
  on all compatible etale scheme charts. Local finite type in the node is explanatory
  setup, not an additional hypothesis or conclusion; its shared chart test is
  `MapIsLocally (@LocallyOfFiniteType)` and is not assumed separately here.
- Affine transitions: for every i,j and f:i⟶j, `MapIsAffine (D.map f).left`.
- Limit as an fppf sheaf over B: `Nonempty (IsLimit
  ((Over.post (ObjectProperty.ι (IsAlgebraicSpace (S := S)))).mapCone
  (Cone.mk (Over.mk p) π)))`. `ObjectProperty.ι` is the actual full-subcategory inclusion
  into fppf sheaves. `Over.post` induces its functor to sheaves over B.obj; `mapCone`
  retains the given projections and cone vertex. Thus the universal property tests
  arbitrary fppf sheaves over B, rather than only algebraic spaces. Being this limit
  gives the stated canonical isomorphism Z ≅ lim Z_i, with the specified B-maps.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsAlgebraicSpace`, `IsRepresentableWith`, `IsEtale`, `IsSurjective`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, `etale_fibreProduct_isScheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
  Their scheme definitions are used through the shared chart predicates; the item does
  not reinterpret the scheme-only definitions directly as predicates on space maps.
- `def-weil-size-convention` is the recorded metatheoretic convention, with no declaration;
  the module explicitly binds u and every variable, with `autoImplicit false`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`,
  `MapIsLocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `IsAbsolutelyQuasiSeparated`.
- `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`: `IsQuasiCompactPresheafMap`, owned
  by the existing:true definition node `def-sfb-space-quasi-compact-presheaf-map`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite`: `MapIsAffine`, owned by
  `def-sfb-space-affine-quasifinite-properties`.
- `Sheaf.AlgebraicGeometry.StackQcqsMorphism`: `IsQuasiCompact`, owned by
  `def-sfb-stack-qcqs-morphism`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom` and the proof input
  `isAffineHom_of_isAffine`.
- `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`: `ObjectProperty.ι`;
  `Mathlib.CategoryTheory.Comma.Over.Basic`: `Over.post`;
  categorical `Cone.mk`, `Functor.mapCone`, `IsLimit`, and the preorder category.

The five landed definition nodes owning chart tests, absolute quasi-separatedness,
the atlas-based quasi-compact presheaf-map predicate, affineness and quasi-compactness
of a sheaf were added to stmt_deps. Their existing Lean is reused unchanged.
Proof-only imports are the recorded modules for relative Spec, affine chart calculus,
affine etale covers and affine-transition scheme limits; the affine-scheme-map Mathlib
match has a plain proof-only import; the statement uses the shared MapIsAffine predicate.
The proof-only nodes `lem-sfb-space-algebra-fp-directed-colimit` and
`lem-sfb-space-affine-locality` have no recorded Lean module at this base, so no import
is invented for them. They remain cited in the proof docstring and the unchanged proof DAG.

Edge cases checked: empty B and Z are permitted (the empty scheme is a quasi-compact
atlas); a singleton directed system is permitted; Nonempty excludes a vacuous empty
inverse system; arbitrary non-quasi-separated S is permitted; p need not be finite type
or finite presentation; neither transitions nor projections are assumed surjective;
no reducedness, noetherianity, nonempty-space, or separation hypothesis is added. The
sheaf-slice limit includes test sheaves that are not algebraic spaces. No extra universe
quantifier can make the test conditions vacuous.

Searches for an existing statement:

- msearch.py leanfinder: "An affine morphism of algebraic spaces over a quasi compact
  quasi separated base is an inverse limit of affine morphisms of finite presentation";
  eight hits, including Scheme.exists_isAffine_of_isLimit, Scheme.exists_isQuasiAffine_of_isLimit,
  isAffineHom_π_app and AffineSpace's local finite presentation instance. All are scheme
  permanence or affine n-space statements, not this algebraic-space existence statement.
- msearch.py leansearch: "An affine morphism of algebraic spaces over a qcqs base is an
  inverse limit of affine morphisms of finite presentation"; eight hits, only scheme
  affine morphisms, scheme limit permanence, and affine-scheme limits, no exact match.
- msearch.py loogle: `"IsAffineHom", "IsLimit"`; zero hits.
- msearch.py grep, subdirectory AlgebraicGeometry:
  `AlgebraicSpace|affine.*limit.*presentation|presentation.*limit.*affine`; zero hits.
- rg in lean/WeilConjectures and lean/Sheaf for the item id, proposed declaration name,
  `affine.*finitePresentation.*limit` and `affine.*finite.*presentation.*limit`:
  scheme results and integral/finite space approximation siblings only; none states
  approximation of an arbitrary affine space map. The nearby integral and finite
  results have stronger hypotheses and do not replace this lemma.
- rg of project definitions found the shared predicates listed above; no new notion or
  private copy was needed. DAG records for all reused notions were opened and read.

The theorem's sole proof is `sorry` as required. No statement dispute was found.

## Repair of returned head 46682d1f56b8

H2: removed theorem node `lem-trf-space-qc-separated-etale-local` from stmt_deps and
replaced it with the live existing:true definition node
`def-sfb-space-quasi-compact-presheaf-map`. The Lean predicate and import for
IsQuasiCompactPresheafMap remain unchanged; the theorem is not a statement dependency.

H4: replaced all three inline affine predicates (p, stages and transitions) with
`MapIsAffine`, and replaced the copied atlas body in hqc with `IsQuasiCompact B.obj`.
Opened and read both live definition modules and their node records; the atlas body is
verbatim the previous hqc. Added their owning definition nodes
`def-sfb-space-affine-quasifinite-properties` and `def-sfb-stack-qcqs-morphism` to
stmt_deps and imported their modules publicly. Updated lean.statement verbatim and
all clause mappings above. No mathematical hypothesis or conclusion changes.

Compared retained sandbox node with current main: outside lean and stmt_deps the node
is unchanged. Regenerated the delivery node from current main, applying only the repaired
lean record and the five used, already-landed definition dependencies. The wrappers
perform delivery rebasing; no direct git command or live-source edit was used.

Validation of this repair is recorded below after the required server checks.

Repair validation: scompile.py compiled both the sandbox module (5.2 s) and actual
library module (11.5 s), with no errors or unexpected warnings. The source contains
one sorry-only theorem, explicitly bound variables and universes, and no new definitions.

## Second reading by N7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
