## Worker report

Item: lem-sfb-rhom-colimit-cohomology-ladder. Module:
`Sheaf.Paper.RHomColimitCohomologyLadder`, namespace
`WeilConjectures.SfbHomFilteredColimit`.

The node is unchanged except for its Lean attachment. Its four mathematical clauses
are stated as four named theorems, all with `sorry`: `ladder_filtered_cohomology`,
`ladder_filtered_consequences`, `ladder_comparison`, and
`rhom_colimit_cohomology_ladder`. All are listed in `lean.declarations` with their
canonical-map helper definitions. No new independent notion, additional node,
dependency repair, or statement correction is needed. The source is Stacks
sites-modules.tex, lemma-limits-colimits (03DB), sites-cohomology.tex,
lemma-RHom-triangulated (08JC), and derived.tex, lemma-cohomology-homological (05RS).
The full eight-step DAG proof is in the main theorem's docstring; the other three
docstrings describe the corresponding parts of that proof.

Hypotheses and objects, clause by clause:

- The site is `{C : Type u} [Category.{v} C] (J : GrothendieckTopology C)`.
  This is the Grothendieck topology of the recorded covering-site convention;
  all constructions depend only on its sheaf category. No extra covering or
  representability property is used. The covering convention module is imported.
- The coefficient is `(R : Sheaf J CommRingCat.{max u v r})`. Commutativity is
  part of its type. Both site universes fit in the coefficient/module universe;
  they are not identified with one another. The usual `HasSheafify` and
  `WEqualsLocallyBijective` instances specify the standard abelian sheaf interface
  available for such small sites. These are the same size assumptions as the
  recorded independent-universe internal Hom, not extra geometric hypotheses.
- `Modules.{u,v,r} J R` is the recorded transparent `ringedSiteModules`
  specialization to the ring sheaf underlying R. No category is reconstructed.
- `CochainComplex (Modules J R) ℤ` and `DerivedCategory (Modules J R)` are the
  ordinary unbounded Mathlib categories. `[HasDerivedCategory.{w} ...]` specifies
  the chosen localization/morphism universe, as in def-weil-size-convention.
  No bounded derived category is substituted.
- `{I : Type (max u v r)} [SmallCategory I] [IsFiltered I]` is any small filtered
  index in the chosen universe. `IsFiltered` includes nonemptiness, common
  cocones for pairs of objects and equalization of parallel arrows. The diagram
  `N : I ⥤ CochainComplex ... ℤ` is completely arbitrary.
- `colimit N` is the actual colimit of complexes. Mathlib's complex-colimit
  construction computes it termwise using sheaf colimits; evaluation at each
  integer preserves it. This is not a colimit in the derived category.
- The fixed models are exactly `homFixed J R P`, hence the recorded functorial
  `coefficientHomResolution J R` followed by `homComplexFunctor.obj (op P)`.
  `ladderModel J R N` takes the termwise colimit of this diagram, naturally
  contravariantly in P. No model for derived Hom is copied or replaced.

The cohomology-colimit assertion is `ladder_filtered_cohomology`: for each integer
q the existing `HomologicalComplex.homologyFunctor ... (.up ℤ) q` preserves colimits
of shape I. `PreservesColimitsOfShape` means that the canonical cohomology cocone
is colimiting, so the resulting isomorphism is natural in diagrams and sends each
colimit injection to cohomology of the complex injection. It is exactly the
claimed H^q(colim K_i) ≅ colim H^q(K_i), with either orientation supplied by the
isomorphism. The theorem concerns all diagrams K, not only N or Hom complexes.

The first conjunct of `ladder_filtered_consequences` quantifies over K,L and
f:K→L and requires `∀ i, QuasiIso (f.app i)` before asserting
`QuasiIso (colim.map f)`. Its second conjunct quantifies over K and a common
integer a, assumes `IsZero H^q(K_i)` for every i and q<a, and concludes
`IsZero H^q(colimit K)` for every q<a. A common bound is explicit; no such bound
is assumed elsewhere.

The comparison alpha is specified by actual data, not an arbitrary comparison:
`ladderStrictAlpha N P` is `Q.map` of
`colimit.desc (N ⋙ homFixed P) ((homFixed P).mapCocone (colimit.cocone N))`,
followed by the inverse of the fixed `coefficientHomResolutionIso`.
`ladder_comparison` asserts that the source functor localizes to F with natural
factorization isomorphism e, and that alpha:F→H(-,QN_infinity) has exactly the
component `e.hom.app (op P) ≫ ladderStrictAlpha N P` for EVERY source complex P.
This is an existence theorem for the fully specified localization presentation,
not a definition choosing an object from mere existence. No data definition
uses a postponed theorem or `sorry`.

For each P and q this theorem also specifies the cohomology-colimit isomorphism
beta by its value on EVERY stage injection: apply H^q to the fixed resolution
comparison followed by Q of the actual Hom-model colimit injection. It then
asserts `beta.hom ≫ H^q(e.inv ≫ alpha) = ladderVertical`.
Thus the vertical arrows in the ladder are H^q(alpha) under precisely the
canonical displayed identification. The factorization and alpha are natural in
the entire derived source category, so using any representative P of a derived
object transports this assertion to arbitrary derived objects. No source
morphism is required to lift to a single chain map.

The distinguished triangle is `(T : Triangle (DerivedCategory ...))` with
`hT : T ∈ distTriang ...`. The objects A,B,C are respectively T.obj₁,T.obj₂,T.obj₃;
u,v,w are T.mor₁,T.mor₂,T.mor₃. The degree q is an arbitrary integer.
`ladderPrecomp f q` is H^q of the recorded derived internal-Hom functor applied
contravariantly to f, naturally in its target. Thus the ordinary horizontal
arrows are exactly precomposition by v and u.

`ladderBoundary T q` is the composite
H^(q-1)H(A,-) → H^q(H(A,-)[-1]) → H^q H(A[1],-) → H^q H(C,-).
The first map is the inverse of Mathlib's cohomology shift isomorphism, the
second is H^q of `RingedHomUniverses.sourceShift J R A 1`, and the third is
precomposition with w. `sourceShift` is the recorded unique source-shift family
normalized by `LeftNormalization` and `LeftFormula`: its Hom-degree-n factor is
`(1*n).negOnePow = (-1)^n`, and it reindexes the source degree. Although the node
writes the reverse isomorphism H(A[1],N)→H(A,N)[-1], the connecting arrow uses
its inverse, exactly as this definition does. The cochain convention is
Mathlib's K[n]^q=K^(q+n), with differential (-1)^n d. The source-shift comparison
is a natural isomorphism of TARGET functors, so these signs are independent of
N and compatible with its transitions.

The rows and all their exact spots are stated in the main theorem:

- `ladderDiagram N X q` is the diagram i↦H^q(H(X,Q(N_i))).
- `ladderColimPrecomp` and `ladderColimBoundary` are the existing colimit functor
  applied to those exact natural transformations. This is the first row.
- Evaluating `ladderPrecomp` and `ladderBoundary` at `Q.obj (colimit N)` gives
  exactly the second row.
- The first three conjuncts assert exactness at C in degree q, B in degree q,
  and A in degree q-1 in the first row. The next three do so in the second row.
  Each uses `∃ h:f≫g=0, (ShortComplex.mk f g h).Exact`, packing precisely the
  existing Mathlib exactness predicate with its zero-composite proof.
  Since q ranges over all integers these are EVERY exact position, including
  exactness at A in degree q and at C in degree q+1 after replacing q by q+1.
- The final three conjuncts assert the commuting v-square, u-square and
  connecting w-square. `ladderVertical N X q` is the universal colimit map of
  the actual target cocone after applying H^q H(X,-). Its identification with
  H^q(alpha) is the normalized statement of `ladder_comparison` above.

There are no hypotheses on boundedness, continuity, constructibility, or
finite generation of A,B,C or N. All four theorem proofs are `sorry`, as required
for stage 2; every helper definition has real, explicit categorical data.

Dependency declarations used (recorded modules read, including signatures and
normalizations):

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; topology/sheaf component is
  the recorded Mathlib `GrothendieckTopology` and `Sheaf` interface.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, localization and triangulation.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`, using the same localization.
- `Sheaf.Paper.DerivedInternalHomFilteredColimitData`:
  `WeilConjectures.SfbHomFilteredColimit.Modules` and `homFixed`.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit`, `colimit.desc`,
  `colimit.ι`, `Cocone`, `IsColimit`; filteredness is `CategoryTheory.IsFiltered`.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`:
  `Triangle`, `distinguishedTriangles`; the derived category has `IsTriangulated`.
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`:
  `RingedHomUniverses.hom`, `sourceShift`, `LeftFormula`, `LeftNormalization`,
  `leftShift_existsUnique`, and the reexported internal-Hom exactness interface.
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation` (reexported by strict
  models): `coefficientHomResolution`, `coefficientHomResolutionIso`.
- Proof imports are `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`
  (`SheafOfModules.grothendieckAbelian_with_localized_generator`),
  `Sheaf.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses`
  (`quasiIso_homComplex_mapOfUniverses`),
  `WeilConjectures.Algebra.Homology.HomComplex` (`homComplex`, `homComplexFunctor`),
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
  (`DerivedCategory.HomologySequence.exact₁`, `exact₂`, `exact₃`), and
  `Mathlib.CategoryTheory.Triangulated.HomologicalFunctor`
  (`Functor.homologySequenceδ_naturality`).
- The metatheoretic size node has no declaration; its universe convention is
  rendered by the explicit u,v,r,w and the bound on the index universe.

Edge cases checked before writing and rechecked against the finished statement:

- A one-object/terminal-object filtered index gives the ordinary Hom exact row
  and canonical cocone comparison, with no extra bound on N.
- The empty category is not filtered (`IsFiltered` includes nonemptiness).
  The empty SITE is allowed; its zero module category causes no type exclusion.
- The zero ring sheaf, zero complexes and contractible or split triangles are
  allowed. Zero connecting maps are correctly obtained from precomposition by
  w=0; exactness is stated in module sheaves, not on bare section sets.
- q can be negative, zero, or positive; q-1 is an integer, not truncated natural
  subtraction. The q+1 connecting square is present by varying q.
- A common lower bound a=0 or a<0 is allowed; diagrams without a common lower
  bound are allowed in every other assertion.
- Infinite products occur inside each Hom complex only. No definition or
  conclusion interchanges such a product with a filtered colimit.
- Site object and morphism universes u and v can differ. r is independent and w
  independently records derived morphism size. No equality u=v is imposed.

Searches (all performed through the prescribed msearch wrapper or read-only rg):

- leanfinder: "Exact filtered colimits commute with cohomology of sheaf module
  complexes and yield the natural derived internal Hom triangle cohomology
  ladder including connecting maps". Eight hits, including MayerVietorisSquare
  exactness, Ext homologySequenceδ evaluations, and
  `DerivedCategory.HomologySequence.exact₃`; none states this whole comparison.
- loogle: `"homologyFunctor", "colimit"`. Zero hits.
- leansearch: "Filtered colimits commute with homology of unbounded complexes
  in an abelian category". Eight hits including `colimitLimitIso`,
  `instPreservesHomologyFunctorAddCommGrpCatColim`,
  `HomologicalComplex.instHasFilteredColimitsOfSize`,
  `HomologicalComplex.isColimitOfEval`, and
  `Functor.preservesHomologyOfExact`. These supply general infrastructure,
  not the specified sheaf internal-Hom comparison or its signed ladder.
- rg of Mathlib Algebra/Homology: `colimit.*homology|homology.*colimit` found
  generic cohomology/local-cohomology infrastructure, no exact whole match.
- rg of both `lean/WeilConjectures` and `lean/Sheaf`:
  `(rhom|RHom|internalHom).*(colimit|colim)|(colimit|colim).*(rhom|RHom|internalHom)`;
  the upstream match was an unrelated affine-perfect tensor roof. The local
  coefficient-colimit statements concern their different scalar-extension
  comparison, not this arbitrary-target diagram and arbitrary source triangle.
- rg of `lean/WeilConjectures` for the item id found nothing. Search for our
  helper/main declaration names in both source trees found no existing names.
- Read the strict model and normalized signed-shift dependency modules directly;
  those reusable notions are imported, not recreated.

Validation: the complete module compiled cleanly on the server via scompile.py
in both sandbox and library modes (15.7 s and 16.4 s in that run); the delivery
dry run also checks the final imports, JSON record, report and per-file compile.
No STATEMENT-DISPUTED condition or node fault was found. The archived example
`Sheaf.CategoryTheory.CompactObject` is withdrawn in the live checkout; its
recorded upstream replacement was read for the module and declaration style.

## Second reading by N8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
