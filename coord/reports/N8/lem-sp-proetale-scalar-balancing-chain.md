## Worker report

This stage-2 delivery states `AlgebraicGeometry.ProEtale.proEtaleScalarBalancingChain`
in `Sheaf.SecSmoothPurity.ProEtaleScalarBalancingChain`. Its sole postponed proof is
that named theorem. The three helper definitions contain real data: the existing
restriction mate inverted with its published IsIso theorem, its conjugation through
the normalized scalar-to-tensor isomorphisms, and the explicit pure-section predicate.
No definitions, actions, coefficient identifications or comparison maps are chosen
from mere existence. The accepted stage-1 split is retained, without re-splitting.
The saved returned delivery is retained and repaired at the two points requested
by the maintainer on immutable head 49085731679a.

Hypotheses and clauses, matched individually:

* Any scheme map: `{X Y : Scheme.{u}} (f : X ⟶ Y)`; there are no geometric hypotheses.
* Finite commutative rings and their unital homomorphism: `{A B : Type u}`,
  `[CommRing A] [CommRing B] [Finite A] [Finite B]`, and `φ : A →+* B`.
* Coefficients and categories: `proEtaleConstantRing`, `proEtaleRingModules`, and
  `proEtaleConstantRingPullback` use the already recorded constant-coefficient
  realization. These are the constant-section-preserving presentation of the
  sheafified continuous-functions coefficient objects, not new coefficient sheaves.
  The small site retains object universe u+1 and morphism universe u; rings/modules
  are in u+1 via the established ULift convention. Finite rings admit this size choice.
* The coefficient maps a_X,a_Y are `proEtaleConstantRingMap φ`; c_A,c_B are
  `proEtaleConstantRingComparison`. The first conjunct is exactly their commuting
  square, with Lean's left-to-right composition order.
* Scalar restriction is `scalarMateRestriction`, the existing abbreviation for
  `proEtaleRingRestrictScalars`, itself Mathlib `SheafOfModules.restrictScalars`.
* Beta is `scalarBalancingBeta`, the inverse of the existing canonical ordinary
  restriction/pullback mate, not an arbitrary comparison. The second conjunct
  specifies its inverse on every inverse-image unit section of every B-module N.
  This expresses identity on the underlying inverse-image sheaf in the library's
  tensor-extension presentation of identified-coefficient inverse image. The unit
  sections locally generate that inverse image; no assertion that all sections are
  global unit images is made.
* The natural family t is an isomorphism of functors from A_Y-modules to
  A_X-modules: `scalarMateOrdinaryTensor φ Y ⋙ proEtaleConstantRingPullback A f ≅
  proEtaleConstantRingPullback A f ⋙ scalarMateOrdinaryTensor φ X`. The ordinary
  tensor functor is the existing sheaf tensor with r(B) as its last factor.
* Its required normalization is exactly `IsScalarBalancing φ f t`. This quantifies
  over every M,V,x,s, uses `proEtaleTensorPair` (the actual presheaf tensor followed
  by the module sheafification unit), applies the module adjunction unit to x⊗s,
  and sends it to the tensor of the unit image of x with the image of s through
  `proEtaleRingDirectImageMap f B_Y B_X c_B`. The latter is eta followed by c_B,
  hence exactly c_B(f^{-1}s). V is pulled back by `proEtaleBaseChange f`.
* Uniqueness applies to every natural isomorphism satisfying that formula alone:
  `∀ t', IsScalarBalancing φ f t' → t' = t`. Thus uniqueness is not conditional on
  extra B-linearity or chain properties of the competitor.
* B_X-linearity is the next conjunct, for every module M, every site object W,
  every b in B_X(W), and every section h of the B-pullback of M⊗B_Y. Its equation
  is `g (b • h) = b • g h`, with `g = scalarBalancingMap φ f t M`. This g is
  beta, then inverse image of the canonical scalar-to-tensor identification, then
  t, then its target identification inverted. It is precisely t beta in the
  existing scalar-extension coordinates, where both genuine B-actions are exposed.
  The explicit `@id` only exposes the target B-module carrier for typeclass search.
* Arbitrary unbounded cochains are quantified as all
  `CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y A)) ℤ`.
  T is a natural isomorphism of the induced complex functors. Its hom and inverse
  in degree i are respectively `t.hom.app (P.X i)` and `t.inv.app (P.X i)`.
  Both are actual chain maps since they are morphisms in the complex category.
* The displayed differential equation is supplied explicitly for every i,j,
  using the two composite functors' maps on `P.d i j`. Their maps are exactly
  inverse image of d⊗1 and inverse image of d tensored with 1.
* The total-tensor clause now compares specified maps, with no existential U.
  The left side is pullback of `mapBifunctorSingle₂Iso.hom`, followed by
  `T.hom.app P`. The right side starts with
  `(Scheme.proEtaleTensorPullbackTotalIso f A_Y A_X c_A P B_Y[0]).inv`.
  This inverse has exactly the required direction from pullback of the total to
  the total of the two pullbacks. Next `HomologicalComplex.mapBifunctorMap`
  leaves the first factor fixed and applies the coefficient complex map to the
  second. That map is `singleMapHomologicalComplex.hom` followed by
  `singleFunctor.map (scalarMateCoefficientPullback φ f).hom`: the latter uses
  the inverse restriction/pullback mate and the normalized B-unit pullback,
  hence exactly the prescribed c_B identification. Finally the target
  `mapBifunctorSingle₂Iso.hom` identifies this total with the degreewise tensor
  complex. Thus the equation tests agreement with the canonical total map
  rather than merely existence of some isomorphism between the same endpoints.
* There is no boundedness, flatness, K-flatness, prime or torsion assumption.

Dependency declarations read and used:

* `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `AlgebraicGeometry.ProEtale.finiteCoefficientRingSheaf`,
  `FiniteCoefficientModules`, `finiteCoefficientRealization` (canonical
  continuous-function presentation and its coefficient realization).
* `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `AlgebraicGeometry.Scheme.proEtaleConstantRingComparison`,
  `proEtaleConstantRingPullback`, `proEtaleConstantRingAdjunction`.
* `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`:
  `AlgebraicGeometry.ProEtale.finiteCoefficientInverseImageMap_isIso`,
  `finiteCoefficientConstantComparison`, with constant and empty-source normalizations.
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, `cochainModulesPreadditive`.
* `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`.
* `Sheaf.Paper.ProEtaleScalarMateNormalization`: `scalarMateRestriction`,
  `scalarMateCoefficient`, `scalarMateCoefficientComplex`, `scalarMateOrdinaryTensor`,
  `scalarMateOrdinaryTensorIso`; its pure-tensor unique characterization was read.
* `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`:
  `proEtaleRingRestrictScalars`, `proEtaleRingRestrictionPullbackInv`, and
  `proEtaleRingRestrictionPullbackInv_isIso` (the actual ordinary beta).
* `Sheaf.Paper.ProEtaleCanonicalTensorPullback`:
  `proEtaleOrdinaryTensor`, `proEtaleTensorPair`.
* `Sheaf.Paper.FourCorners`: `proEtaleRingExtension`, the existing ordinary
  sheafified scalar-extension functor, without the adic hypotheses of later uses.
* `Sheaf.Paper.StratumScalarExtension`: `proEtaleConstantRingMap`.
* `WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle`:
  `CochainComplex.mapBifunctorSingle₂Iso`, whose full construction was read.

Definition ownership is explicit in stmt_deps. The scalar identifications cite
`def-sp-proetale-scalar-mate-identifications`; the plain restriction/pullback
comparison cites `def-weil-pbc-ring-restriction-pullback-comparison`. The theorem
`lem-weil-pbc-ring-sheaf-change-adjunction` remains because
`proEtaleRingRestrictionPullbackInv_isIso` is used by `asIso` in the definition
of beta. The plain tensor/pairing/total constructions and constant-ring map
are owned by the two new existing:true definition nodes below. The former
scalar-mate normalization, derived tensor pullback and stratum-scalar-extension
theorems are not cited as assumptions merely to obtain their definitions.
The existing four-corners definition node owns ordinary scalar extension.
There are no dependency replacements, statement corrections or disputed statements.
The mathematical node statement is unchanged; R2 repairs its Lean encoding.
All recorded statement modules are imported publicly. Every stated proof-dependency
module is imported; the trilinear proof node has no Lean record and so no module
can be imported for it. No part of the signature requires that missing declaration.

Edge cases checked mathematically against Stacks 03EL: identity scheme map and
identity ring map give the standard tensor comparisons; empty X gives zero sheaves;
B the zero ring gives zero scalar extension; non-flat Z/4 → Z/2 needs no exactness
of extension; A and B need not have the same characteristic. P may have nonzero
terms in arbitrarily large positive and negative degrees: tensor by B[0] still has
only (i,0) in degree i. The formula uses sheafification images of pure tensors and
never assumes every sheaf-tensor section is pure.

Sources opened: `literature/stacks-project/sites-modules.tex`,
lemma-tensor-product-pullback (03EL), including its bilinear adjunction proof;
012Z total-complex normalization as in the DAG's final proof step. The theorem
contains the accepted eight-step natural-language proof in its docstring.

Searches:

* LeanFinder: inverse image of sheaves of modules commutes with extension of constant
  scalars, coefficient actions and unbounded complexes — eight hits on free-module
  pullback, none the complete statement.
* LeanFinder: inverse image sheaf tensor product natural isomorphism scalar extension —
  eight hits on free-module/presheaf tensor comparisons, none the complete statement.
* Loogle: `SheafOfModules.restrictScalars, SheafOfModules.pullback,
  CochainComplex.mapBifunctor` — zero hits.
* msearch grep: `pullback.*[Tt]ensor|[Tt]ensor.*pullback|[Rr]estrictScalars.*[Pp]ullback`
  in Mathlib Algebra/Category/ModuleCat — zero hits.
* rg in project Sheaf and WeilConjectures sources found the scalar-extension mate,
  its derived normalization, and the ordinary tensor identification reused here.
  No declaration states this node: the parent scalar-tensor normalization only
  supplies a representative chain clause under flat-term K-flat hypotheses, while
  this node concerns every complex and separately specifies uniqueness and B-action.
* rg for the node id in upstream WeilConjectures — no match. Read the exact source
  signatures/docstrings of all interfaces listed above. Raw msearch responses are
  preserved in sandbox/searches.jsonl.

Validation: server scompile is used exclusively. The preliminary full signature
compiled; line-length warnings were repaired before the final compile and preflight.

## Returned-delivery repair

R1: Replaced the three theorem-only citations used for plain definitions by their
owning definition records. Added the existing scalar-mate-identifications and
ring-restriction-pullback-comparison definition nodes. Added the two existing:true
ownership nodes below without copying or changing any library construction.
The ring-sheaf-change-adjunction theorem remains for its actual IsIso proof used
by beta; this is the typing use the return explicitly accepted.

R2: Removed the existential U and its automatically satisfiable square. The final
conjunct now equates the degreewise chain comparison to the published canonical
signed-total comparison, the c_B coefficient pullback on the second factor, and
the single-factor total identification. The canonical total is oriented from
total of pullbacks to pullback of total, so its inverse is the map needed here.
The coefficient map is the same one used by scalarMateDerivedCoefficientPullback
before localization; there is no arbitrary coefficient identification.

## New nodes

`def-sp-proetale-ordinary-tensor-pullback-total` records the existing
`Sheaf.Paper.ProEtaleCanonicalTensorPullback` definitions `proEtaleOrdinaryTensor`,
`proEtaleTensorPair`, `proEtaleOrdinaryTensorPullback`, `proEtaleTensorPullbackTotal`
and `proEtaleTensorPullbackTotalIso`. Source: Stacks 03EL and the signed total
construction 012Z. The ordinary comparison is selected from a unique natural
unit-section characterization; the total is the sum of its inverse bidegree
maps. The definition node imposes no K-flat or boundedness assumptions and does
not own or assume the later derived tensor theorem. Read its complete published
source, also through scompile.py --source, and the local Stacks sources.

`def-sp-proetale-constant-coefficient-ring-map` records the existing
`AlgebraicGeometry.Scheme.proEtaleConstantRingMap` in
`Sheaf.Paper.StratumScalarExtension`. Its data are precisely the constant-sheaf
functor applied to `CommRingCat.ofHom (RingHom.ulift φ)`; arbitrary commutative
rings are allowed. Its source is the constant-coefficient specialization of 03EL.
This records the construction itself without invoking the stratum theorem.

For both nodes, searches were made before writing the records: LeanSearch for
canonical tensor pullback and signed total complexes returned ordinary pullback
and unrelated tensor infrastructure; LeanFinder for constant-ring maps and total
pullback returned eight generic module-pullback/free-module results; msearch grep
for the four exact construction names found no Mathlib declarations. The raw
service records are in each node's mathlib_searches and sandbox/searches.jsonl.
`rg` of WeilConjectures found no match; `rg` of Sheaf found exactly the published
modules reused. DAG name searches found their old theorem records and consumers,
but no definition owner. A further targeted LeanSearch query for the constant
sheaf ring homomorphism found `CategoryTheory.constantSheaf`, exactly the generic
functor used by the existing specialized map; that result is recorded in its node.
blueprint_refs.py search for tensor pullback and constant
ring map each returned zero blueprint nodes. These are ownership records with
existing:true; no new module or duplicate mathematical definition is introduced.

## Self-check after repair

Re-read the saved signature, current sources and all R1/R2 changes against the
node. Clauses preceding the total equation retain their exact signatures and
hypotheses. Rechecked total-comparison direction, single-complex transport,
coefficient identification and chain endpoints. The identity map, empty scheme,
zero coefficient ring, non-flat Z/4 → Z/2, and unbounded-complex cases retain their
meaning: every total summand with second degree nonzero vanishes for B[0].
The 012Z signed total uses p+q=n and d_h+(-1)^p d_v; the latter differential is
zero for the single coefficient complex. There is no independent second worker
in this dispatcher session; the maintainer performs the independent review.

Validation of the repair: the revised delivered module compiled through
scompile.py as both sandbox and library module (12.0 s / 21.8 s), without errors
or non-sorry warnings. The initial saved-packet dry run passed structurally;
R1/R2 have nevertheless been repaired explicitly rather than repushed unchanged.

The repair dry run caught a truncated lean.statement metadata signature (the
extractor stopped at a named-argument assignment). Replaced the metadata with
the complete theorem signature up to its proof assignment; no Lean change.

## Second reading by N8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
