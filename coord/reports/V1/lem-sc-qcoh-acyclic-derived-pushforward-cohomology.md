## Worker report

The module states `AlgebraicGeometry.qcoh_acyclic_derived_pushforward_cohomology`, with
only `sorry` as proof. The node is unchanged except for its `lean` record. No missing
notion, unusable dependency, or statement correction was needed.

Hypothesis and conclusion correspondence:

- Schemes X and Y: `{X Y : Scheme.{u}}`; the scheme morphism is `(f : X ⟶ Y)`.
- Quasi-compact and quasi-separated morphism: `[QuasiCompact f] [QuasiSeparated f]`.
  These are properties of the morphism; no absolute compactness or separatedness is assumed.
- Every quasi-coherent O_X-module F: `∀ (F : SheafOfModules.{u}
  (moduleRings X.toRingedSpace)), F.IsQuasicoherent → ...` in `hacyc`.
- Every positive degree p and vanishing of R^p f_*F: `∀ (p : ℤ), 0 < p →
  IsZero ((schemeModuleHigherDirectImage f p).obj F)`.
  Positive integers and positive natural degrees index precisely the same higher images.
- E in unbounded D_QCoh(O_X): both functors have domain
  `(schemeDerivedQCohProperty X).FullSubcategory`, through its inclusion `.ι`.
  This is the recorded `schemeDerivedQCohCategory X`; no boundedness binder occurs.
- Every integer i: `(i : ℤ)`.
- H^i(Rf_*E): the left functor is `.ι ⋙ schemeHigherDirectImage f i`.
- f_*H^i(E): the right functor is `.ι ⋙ DerivedCategory.homologyFunctor ... i ⋙
  RingedSpace.moduleDirectImage f.toLRSHom.toShHom`.
- An isomorphism natural in E: `Nonempty (leftFunctor ≅ rightFunctor)` is existence of
  a natural isomorphism, whose components give the claimed sheaf isomorphisms for every E.
  It includes naturality for every morphism in the full quasi-coherent derived subcategory.

Dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-pc-derived-direct-image`: `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`,
  declarations `AlgebraicGeometry.schemeHigherDirectImage` and
  `AlgebraicGeometry.schemeModuleHigherDirectImage`, with
  `AlgebraicGeometry.schemeDerivedDirectImage` appearing through their definitions.
- `def-pc-derived-category`: `Sheaf.AlgebraicGeometry.DerivedCategory`, declarations
  `AlgebraicGeometry.schemeDerivedCategory`, `AlgebraicGeometry.schemeDerivedQCohProperty`,
  and its full subcategory `AlgebraicGeometry.schemeDerivedQCohCategory`.
- Ordinary pushforward is the shared `AlgebraicGeometry.RingedSpace.moduleDirectImage`
  in `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage`, transitively imported through
  the recorded scheme derived direct image. No private pushforward definition is introduced.

The full signatures and docstrings of these declarations were read. The module uses the
shared Mathlib abelian structure, with explicitly bound derived-localization universes wX
and wY, independently. Universe u and all variables are explicitly bound.

Edge cases checked before writing: the zero derived object yields zero on both sides;
identity maps give the usual identity comparison; affine maps satisfy the acyclicity
hypothesis; empty schemes and zero sheaves are permitted. Degree zero is not incorrectly
required to vanish in hacyc. Negative i and objects unbounded in either direction are
included. No assumption on the characteristic, Noetherianity, or compactness of Y is added.
The cohomology comparison concerns O_Y-module sheaves, not just underlying abelian groups.

Source reading: the local Stacks checkout is absent on this machine, so read official
pages https://stacks.math.columbia.edu/tag/08D4,
https://stacks.math.columbia.edu/tag/08D5 and
https://stacks.math.columbia.edu/tag/0AVW. The latter proof displays the comparison for
affine maps; the node's general acyclic qcqs case follows by the same N=1 application
on affine opens. The declaration docstring records all three node proof steps, including
the section comparison, identification of the presheaf, and sheafification/naturality.

Searches for an existing declaration:

- msearch LeanFinder: "Cohomology of unbounded derived pushforward equals pushforward of
  cohomology when higher direct images of quasi-coherent sheaves vanish". Eight hits on
  ordinary site/module pushforward composition and natural isomorphisms, none the theorem.
- msearch Loogle: "Functor.rightDerived, DerivedCategory.homologyFunctor". Zero hits;
  the service reports unknown identifier Functor.rightDerived.
- msearch LeanSearch: "higher direct images vanish quasi coherent cohomology derived
  pushforward". Service unavailable, Internal Server Error; no verdict inferred.
- msearch Mathlib grep: "rightDerived|mapDerivedCategoryFactors" under Algebra/Homology.
  Hits concern bounded-below derived functors and derived exact-functor factorization,
  not the unbounded quasi-coherent acyclicity theorem.
- rg over WeilConjectures and lean/Sheaf: the item id, `acyclic.*(pushforward|Pushforward)`,
  `schemeHigherDirectImage`, `schemeDerivedQCoh`, and
  `qcoh_acyclic.*|acyclic_derived_pushforward|homology.*DirectImage|DirectImage.*homology`.
  No declaration states this node. The landed
  `AlgebraicGeometry.qcoh_acyclic_derived_sections_comparison` states the affine-basis
  presheaf comparison and sheafification identification, rather than the final natural
  isomorphism of O_Y-module sheaves. It is already a proof dependency of the item.
  Upstream direct-image homology comparisons concern restrictions and complexes computing
  higher images in cohomology/base change, rather than this unbounded comparison.

Validation: lcompile.py compiled the single module cleanly (exit 0, no warnings).


## Second reading by V1

Independent second reading, 2026-10-12. No mathematical or Lean mismatch was found;
the module and node signature were left unchanged. Only this review was added.

Object, hypothesis, and conclusion inventory, matched clause by clause:

1. Schemes X and Y and a scheme morphism f: `{X Y : Scheme.{u}}` and
   `(f : X ⟶ Y)`. PASS. Read Mathlib's Scheme and Scheme.Hom: locally affine
   locally ringed spaces and morphisms of locally ringed spaces, as def-pc-scheme.
2. f quasi-compact and quasi-separated: `[QuasiCompact f] [QuasiSeparated f]`.
   PASS. Read the actual classes: compact inverse images of compact opens, and
   quasi-compact diagonal. These are relative conditions on f, not absolute
   conditions on X or Y and not hollow identity-map hypotheses.
3. Every quasi-coherent O_X-module F: `hacyc` quantifies over
   `SheafOfModules.{u} (moduleRings X.toRingedSpace)` and assumes
   `F.IsQuasicoherent`. PASS. Mathlib's latter class means locally a cokernel
   between sums of copies of the ring sheaf, not coherence or finite presentation.
4. Every positive degree p has R^p f_* F = 0: `∀ (p : ℤ), 0 < p →
   IsZero ((schemeModuleHigherDirectImage f p).obj F)`. PASS. Read
   def-pc-derived-direct-image and all three definitions in SchemeDerivedDirectImage:
   the module is placed in degree zero, pushed forward in the unbounded derived
   category, and its p-th cohomology taken. Positive integers give exactly the
   positive natural degrees; IsZero is zero in the category of O_Y-module sheaves.
5. E ranges over all unbounded D_QCoh(O_X): `(schemeDerivedQCohProperty X).ι`
   has source the full subcategory `schemeDerivedQCohCategory X`. PASS. Read
   def-pc-derived-category and DerivedCategory.lean: its property quantifies over
   all integer cohomology sheaves with no boundedness requirement.
6. Every integer i: `(i : ℤ)`. PASS, independently of E. Existence of a natural
   isomorphism for each i is precisely existence natural in E, with no asserted
   compatibility between different degrees.
7. H^i(Rf_*E): the left functor `.ι ⋙ schemeHigherDirectImage f i`. PASS.
   Read the underlying ringed-space direct-image definitions: moduleDirectImage
   is Mathlib pushforward along inverse-image opens with the scalar map f-sharp;
   derivedModuleDirectImage is its unbounded rightDerivedFunctor, computed by
   the shared K-injective construction, not a bounded-below replacement.
8. f_*H^i(E): the right functor `.ι ⋙ DerivedCategory.homologyFunctor ... i ⋙
   RingedSpace.moduleDirectImage f.toLRSHom.toShHom`. PASS. Same module carrier
   and ordinary pushforward as in the dependency; no private definitions.
9. Isomorphism natural in E: `Nonempty (leftFunctor ≅ rightFunctor)`. PASS.
   This is a natural isomorphism, not merely objectwise isomorphisms; components
   and naturality cover every object and morphism of the full subcategory.
10. The two HasDerivedCategory binders choose the localization supplied by the
    recorded derived-category construction. PASS. Read Basic.lean: the standard
    localization is available in max(object universe, morphism universe). They
    express the existing shared construction, not finiteness or existence of
    special resolutions assumed only for this theorem. u, wX, wY are bound;
    wX and wY are independent. No other implicit mathematical assumptions occur.

Source verification: the repository has no Stacks checkout. Downloaded the official
Stacks perfect.tex to the item's scratchpad and read
lemma-application-nice-K-injective (08D4), lemma-quasi-coherence-direct-image (08D5),
and lemma-affine-morphism-equivalence (0AVW), together with their proofs. Also read
[08D4](https://stacks.math.columbia.edu/tag/08D4),
[08D5](https://stacks.math.columbia.edu/tag/08D5), and
[0AVW](https://stacks.math.columbia.edu/tag/0AVW).
08D4 has no Noetherian, field, characteristic, or boundedness assumptions.
For the node's general acyclic qcqs case, the higher-image hypothesis, Leray,
quasi-coherence of f_*F, and affine vanishing supply its N=1 section hypothesis;
section functors preserve products. Applying its truncation comparisons with
both cutoffs i reduces to H^i(E). The local proof in 08D5 and the display in 0AVW
justify the node's comparison; affineness of f is used in 0AVW to establish
acyclicity and need not be added to this node's explicit hypothesis.
The module docstring records all three node proof steps and their cited nodes.

Edge cases: no index set occurs. Zero sheaves and the zero derived object are
allowed; there is no Nonzero or Nonempty binder on schemes, so empty schemes are
allowed. p=0 is deliberately outside hacyc; i=0, negative i, and unbounded positive
and negative tails of E remain included. General commutative structure rings,
all characteristics, and arbitrary scheme universe u are admitted. No absolute
quasi-compactness of Y, separatedness, Noetherianity, or finite type is added.

Independent searches (different phrases from the first reading):

- LeanFinder via msearch: "acyclic quasi-coherent modules imply t exact unbounded
  right derived direct image". Eight hits: acyclic homotopy complexes, Ext under
  exact functors, injective/projective derived vanishing, exact localization, and
  mapDerivedCategoryFactors. None states this quasi-coherent right-derived
  pushforward theorem; the latter requires an exact functor on the whole category.
- Loogle via msearch: "CategoryTheory.Functor.rightDerivedFunctor". Unknown
  identifier in the public index; no usable match, not a negative existence proof.
- LeanSearch via msearch: "t exact derived pushforward quasi coherent sheaves".
  Service returned Internal Server Error; unavailable, no mathematical verdict.
- rg on Mathlib, the entire WeilConjectures source and repository lean/Sheaf,
  using acyclic, homology/pushforward, direct-image/isomorphism and
  schemeHigherDirectImage/qcoh_acyclic. No existing exact statement. Opened
  QCohAcyclicDerivedSectionsComparison.lean: it compares presheaves on affine
  opens and their sheafification, rather than the claimed final sheaf isomorphism.
  Upstream ordinary higher-image restriction and sections results concern modules,
  while compactly supported etale cohomology concerns different coefficients/sites.
  None can be recorded as existing for this node.

No new definition nodes, dependency modules, or statement corrections are in the
delivery, so H12/H13 and corrected-citer checks do not apply. There is one named
statement with proof `sorry`, no definitions to be hollow, no private notation or
instances, and imports supply precisely the used functors and morphism properties.
The module has the required source and blueprint docstrings and no overlong lines.
The recorded lean.statement agrees verbatim with the declaration signature.
Local validation: lcompile.py, exit 0, no errors or warnings. Server compilation
and preflight are run by deliver2.py as the final delivery checks.
