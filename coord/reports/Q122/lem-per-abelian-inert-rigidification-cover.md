## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianInertRigidificationCover` states
`AlgebraicGeometry.GabberModification.exists_abelian_inert_rigidification_cover`
with `sorry`. The natural-language item statement is unchanged. The auxiliary
module defines the additional divisorial, eigenparameter, induction, and pullback
predicates with actual formulas; no definition contains `sorry` or chooses an
object from an existence theorem. Universes `u` (schemes and geometric fields)
and `v` (groups) are independent and explicitly bound. Both auto-implicit options
are disabled in the two new modules.

I read ILO VIII 5.3.1--5.3.7 directly from printed pp.123--125. Lemma 5.3.5
supplies the local eigenparameter construction; 5.3.7 supplies the strict inert
affine cover, induction and finite-cover argument; 5.3.6 specifies inertia
preservation. The last local pullback clause is the node's sixth proof step,
using ordinary Cartesian pullback and the same local construction. The theorem's
docstring retains all six proof steps, including the extra component-deletion
shrink in the reviewed node. Nothing is proved at this stage.

Hypothesis correspondence:

| Node hypothesis | Lean rendering |
| --- | --- |
| A scheme and finite group acting | `X : Scheme.{u}`, `{G : Type v} [Group G] [Finite G]`, `a : G →* Aut X` |
| Noetherian | `hnoeth : IsNoetherian X` (locally Noetherian and compact) |
| Quasi-excellent | `hqe : QuasiExcellent X`, testing every affine-open ring |
| Regular | `hreg : IsRegularScheme X`, the recorded locally Noetherian stalkwise predicate |
| Separated | `hsep : X.IsSeparated` |
| Boundary is strict normal crossings | `B : X.IdealSheafData`, `hsnc : IsStrictNormalCrossingsBoundary B` |
| Boundary is G-strict | `hstrict : GStrict a B` |
| Action on the pair | `hinvariant : ∀ g, B.comap (a g).hom = B` |
| Tame | `htame`, invertibility in each algebraically closed geometric field of the cardinal of its actual stabilizer |
| Free off B | `hfree`, a geometric stabilizer element is 1 when the point is outside `B.support` |
| Abelian geometric inertia | `habelian`, commutation of any two elements fixing each geometric point; the entire group is not assumed abelian |

Conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Ordinary input scheme, with its canonical divisorial log structure | Existential `L`, `e : L.scheme ≅ X`, `aL`, `DivisorialBoundary L (B.comap e.hom)` and the displayed action transport equation. No log structure is added to the input hypotheses. |
| G-equivariant affine etale surjective cover | Existential `U`, `b`, `f : EtaleLogHom U L`; `IsAffine U.scheme`, `Etale f.base`, `Surjective f.base`; `Inert` includes log equivariance. The map to X is `f.base ≫ e.hom`. |
| Strict and inert for the old boundary | `f.IsStrict`, `Inert b aL (MonoidHom.id G) f`, and the actual `DivisorialBoundary U` for `B.comap (f.base ≫ e.hom)`. Strictness uses the canonical characteristic-stalk map; `Inert` is bijectivity on geometric stabilizers. |
| An enlarged invariant SNC boundary | `R : Rigidification b` retains `R.boundary`, `R.snc`; `R.HasEigenparameters` adds equality of its divisorial sheaf, invariance under every group element, and inclusion of the old boundary support. Since both boundaries are reduced, the support inclusion is exactly inclusion of these divisors. |
| Very tame, fs log regular | `R.veryTame` is `R.action.IsVeryTame`; `R.enlarged` is an fs log scheme and `R.logRegular` is its log regularity. The existing very-tame predicate includes tame geometric inertia, trivial characteristic action, and identity on the strict-local stratum quotient. |
| Finite induction from inertia neighborhoods | `HasFiniteInertiaInduction b`: affine subgroup pieces, equivariant open immersions, all translates cover, translates are disjoint for different pieces or left cosets, and every subgroup is realized as inertia at a geometric point of its piece. These give the actual induced scheme/action presentation. |
| Local eigenparameters after adjoining roots of unity | `HasLocalEigenparameters`: for every geometric point, its actual subgroup H, an affine H-equivariant etale neighborhood with an H-fixed geometric lift, fixed primitive root of order `Nat.card H`, invertible order, and invertible nontrivial root differences. Germs of the functions are a full regular parameter list. Both ideal equations are products of distinct parameters. Characters take values in the specified cyclic roots and satisfy exact eigenfunction equations. |
| Strict inert etale pullback again has local rigidifications | `R.PullsBack (a := aL) f ...`: all strict inert equivariant etale maps `q` are quantified. Both the old and enlarged diagrams are genuine scheme pullbacks, and their log squares commute. The old projection is surjective strict inert etale; both comparison maps are strict inert etale. The enlarged source retains log regularity, very tameness, its prescribed pulled-back divisorial boundary, locally SNC on affine opens, and eigenparameters for both pulled-back boundaries. Its forgetful map is an equivariant underlying-scheme isomorphism. |

The pullback assertion is local: it imposes neither global affineness nor globally
finitely many irreducible boundary components on an arbitrary non-quasicompact
etale base change. It quantifies over identity maps as well as arbitrary strict
inert etale maps. Its input target action is explicitly `aL`; no action is inferred
from an unrelated hypothesis.

Recorded dependency declarations used:

- `Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent`;
  `Sheaf.AlgebraicGeometry.GabberModificationData`: the affine-local
  `GabberModification.QuasiExcellent` wrapper.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`.
- `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`:
  `IsStrictNormalCrossingsBoundary` (reduced Cartier ideal, integral regular
  components and expected-codimension regular intersections).
- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`:
  `FineSaturatedLogScheme`, `EtaleLogHom`, `FineSaturatedLogScheme.IsLogRegular`.
- `Sheaf.AlgebraicGeometry.GabberModificationData`: `GStrict`, `Inert`,
  `Rigidification`. Its existing invariance, SNC, very-tame and log-regular fields
  are reused, not copied into a private replacement notion.
- `Sheaf.AlgebraicGeometry.FSLogGroupAction`: `FSLogGroupAction` and
  `FSLogGroupAction.IsTame` (the ordinary-input formula matches this definition).
- `Sheaf.AlgebraicGeometry.VeryTameFSLogAction`:
  `FSLogGroupAction.IsVeryTame`.
- `Sheaf.AlgebraicGeometry.FSStrictLogMorphism`: `EtaleLogHom.IsStrict`;
  `Sheaf.AlgebraicGeometry.LogMorphismOperations`: `EtaleLogHom.comp`.
- `Sheaf.AlgebraicGeometry.LogRegularPair`: `divisorialLogPresheaf`,
  `divisorialStructuralMap`; the boundary-complement inclusion is explicitly
  `Scheme.Opens.ι (X := X.scheme) B.support.compl`.
- `WeilConjectures.RingTheory.IsRegularSystemOfParameters`:
  `IsLocalRing.IsRegularSystemOfParameters`, including the zero-dimensional case.
- `Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots`: `IsPrimitiveRoot`;
  Mathlib's `IsPullback`, `Etale`, `Surjective`, `IsOpenImmersion`, `IsAffine`,
  `Subgroup`, `Subgroup.zpowers`, and `Ideal.span` retain their usual meanings.

Edge cases checked before retaining the statement: empty input scheme (zero
induction pieces, no geometric points, empty parameter obligations); trivial
inertia (root of order 1 and no nontrivial root differences); dimension zero
(empty parameter list); empty boundary (empty product is 1); disconnected schemes
(the group need not be abelian); arbitrary universes for the finite group;
and non-quasicompact or nonseparated etale base changes (only local boundary
conditions). The two boundary subsets may overlap; each separately has no repeated
parameter. Old boundary inclusion is support inclusion between reduced divisors.

Searches, including fresh retries on 2026-10-24:

- LeanFinder: "Strict inert affine etale cover with very tame enlarged boundary
  and eigenvector regular parameters". Eight standard-etale presentation results,
  including `StandardEtalePresentation` and ordinary smooth/etale presentations;
  none states this theorem or its additional predicates.
- LeanSearch: "Local eigenparameters for abelian inertia actions preserving strict
  normal crossings divisors". Eight ordinary number-theoretic inertia-degree and
  eigenspace results; no local scheme predicate.
- Loogle: `AlgebraicGeometry.IsStrictNormalCrossingsBoundary,
  IsLocalRing.IsRegularSystemOfParameters`. No hits; the project identifier is
  unknown to the Mathlib service. The recorded project declarations were read
  directly and reused.
- msearch grep, Mathlib AlgebraicGeometry:
  `rigidification|eigenparameter|GStrict|veryTame`. Zero hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `eigenparameter|eigenvector.*parameter|HasLocalEigenparameters|HasFiniteInertiaInduction|DivisorialBoundary`
  found no declaration. Searching for `GStrict`, `Inert`, `QuasiExcellent`, and
  `Rigidification` found their unique provider in `GabberModificationData`.
  The exact item-id search found no upstream matching theorem.
- DAG search for `eigenparameter|eigenvector regular system` found the present
  theorem and related comparison/coordinate theorems, not an existing definition
  of the extra data. `tools/blueprint_refs.py search eigenparameter` found no
  blueprint definition; `search rigidification` found only unrelated Picard
  nodes. `ancestor` identifies `lem-per-artin-gabber-affine-curve`.

The service results are preserved verbatim in the new node's `mathlib_searches`.
There is no exact existing theorem. No statement correction or mathematical
counterexample is asserted.

## New nodes

`def-per-inert-eigenparameter-rigidification-data` owns
`InertEigenparameterRigidificationData.lean` and its five predicates:
`DivisorialBoundary`, `HasLocalEigenparameters`, `HasFiniteInertiaInduction`,
`Rigidification.HasEigenparameters`, and `Rigidification.PullsBack`. Their formulas
are described clause by clause above and in the self-contained node statement.
Sources: ILO VI 1.1, 1.4, 3.1 and VIII 5.3.3--5.3.7. The existing Gabber data already
own the underlying rigidification, inertia and G-strictness notions; this new node
only adds the divisorial identification, eigenfunctions, induction presentation,
and local pullback assertions required by this item. The three kinds of searches
above found no existing owner for these additional predicates. Its definition
node cites the existing providers and introduces no theorem or arbitrary choice.

## Dependency modules

`def-trf-strict-etale-log-blowup-procedure` owns the supplied
`StrictEtaleLogBlowupProcedure.lean`. The earlier attempts repeatedly hit
`cannot import non-module StrictEtaleLogBlowupProcedure from module` while loading
`GabberModificationData`, even though `scompile.py --source` returned module-mode
source. A fresh ordinary-import probe still reproduced that error in this retry.
Supplying the current source under its actual module path to `scompile.py` makes
it a private module overlay, and then the existing `GabberModificationData`
consumer compiles and exposes the required declarations. The supplied source
agrees with the current server source in every definition, field and body; the
only source change is a blank line after `module`. Its record is repaired only in
`lean`, with an explanatory note. No published source/artifact or launcher script
was edited. The item cites this landed dependency explicitly, as well as the
existing Gabber data node.

The earlier retained drafts also needed the explicit scheme argument to the
boundary-complement inclusion and the explicit target action in `R.PullsBack`.
Both repairs are in the delivered modules. Primitive root differences are units,
so the root remains primitive in every residue field of the chosen neighborhood,
including when it is disconnected. Every supplied file is compiled separately by
the required server wrapper. The initial missing item JSON and Lean record have
been restored; the earlier blocker history is superseded by this validated packet.

## Second reading by Q122

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
