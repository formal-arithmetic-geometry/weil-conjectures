## Worker report

States `AlgebraicGeometry.Etale.ctf_hom_locallyConstant` in
`Sheaf.Paper.CtfHomLocallyConstant`, with proof exactly `sorry`.
The statement follows ILO XVII Lemma 7.6.11 (printed p. 314), read directly in the
local PDF, together with Definitions 7.3.1--7.3.3 (pp. 303--304).
No statement correction or disputed statement is needed.

Clause-by-clause correspondence:

- Prime ell and Lambda=F_ell: `(l : ℕ) [Fact l.Prime]`; the coefficient hypothesis is
  `[Algebra (ZMod l) A]`. The ground-ring refinement predicate uses
  `ULift.{u+1} (ZMod l)`, the same field transported to the module universe.
- Noetherian scheme: `(X : Scheme.{u}) [IsNoetherian X]`, including the empty scheme.
- Commutative Noetherian Lambda-algebra: `(A : Type (u+1)) [CommRing A]
  [IsNoetherianRing A] [Algebra (ZMod l) A]`; A need not be finite as a set.
- Ordinary small-etale module sheaves and derived objects: `Sheaf X.smallEtaleTopology
  (ModuleCat.{u+1} A)` and `DerivedCategoryModule A X`. These are the recorded
  fixed-coefficient presentation; schemes have universe u, site objects u+1 and arrows u.
- F locally constant, constructible: `Scheme.IsFiniteLocallyConstantSheaf F` means
  etale-local constancy together with finitely generated geometric stalks. For a locally
  constant sheaf on a Noetherian scheme, this is equivalent to locally constant and
  constructible as in the node. It does not require a finite global trivializing cover.
  On a trivializing chart the constant module is a geometric stalk; conversely its
  finite generation gives all stalks finite type. Such charts give a constructible
  local system, or one uses the one-stratum finite-type constructibility predicate.
- Flatness is `exactFunctor _ _ (tensorLeft F)`: preservation of finite limits and
  finite colimits for ordinary sheaf tensor, exactly exact tensor with F.
- Every Galois partition P: `∀ P : Scheme.GaloisPartition X`.
- One partition P' independent of interval and complex: the `∃ P'` occurs before
  `∀ (a b : ℤ)` and `∀ N`.
- Refinement: `P'.Refines P (ULift.{u+1} (ZMod l))` is inclusion of the weak classes
  over the ground field, precisely Definition 7.3.3. No stronger maps-of-covers
  condition is imposed.
- All u<=v and N in D^b_P intersect D^[u,v]: bind `a b`, `a ≤ b`, `N`,
  `P.boundedDerived A N`, and vanishing `IsZero (H^q N)` for `q<a ∨ b<q`.
- Derived internal Hom from a sheaf: `derivedHom` applied to the opposite of
  `(_root_.DerivedCategory.singleFunctor _ 0).obj F`, then to N. This is the
  existing ordinary-etale internal Hom exposed by def-pur-derived-internal-hom.
- Output membership and same interval: `P'.boundedDerived A` of that object, and
  `IsZero` of its cohomology outside `[a,b]`, with both endpoints included.
- Constructibility: `DerivedCategory.constructibleHomology ... N →
  DerivedCategory.constructibleHomology ... (RHom(F,N))`. Both objects already have
  bounded cohomology by the interval clauses. Its definition is finite locally closed
  stratification with finite-type local systems, allowing infinite underlying modules.
- No dualizing hypothesis occurs.

Dependency declarations inspected and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` and its morphisms;
  Mathlib.AlgebraicGeometry.Sites.Etale: `Scheme.smallEtaleTopology`;
  Mathlib.AlgebraicGeometry.Noetherian: `IsNoetherian`;
  Mathlib.RingTheory.Noetherian.Defs: `IsNoetherianRing`;
  Mathlib.RingTheory.Finiteness.Defs: `Module.Finite`.
- WeilConjectures.AlgebraicGeometry.DerivedCategories (read with `scompile.py --source`):
  the ordinary `DerivedCategoryModule`, `DerivedCategory.homologyFunctor` and boundedness.
- Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification:
  `Scheme.FiniteLocallyClosedStratification`, directly extended by the new partition.
- Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules:
  retains `SheafOfModules.IsLocallyConstantFiniteTypeModules` unchanged and now exposes
  `Scheme.IsFiniteLocallyConstantSheaf` and `Scheme.IsConstructibleSheaf` from the
  existing WeilConjectures.ConstructibleSheaf.Defs (see dependency repair below).
- Mathlib.CategoryTheory.Limits.HasLimits and Filtered.Basic: `Cocone`, `IsColimit`,
  `IsFiltered`, used to express an actual filtered colimit without an arbitrary chosen map.
- Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses exposes the existing
  `AlgebraicGeometry.Etale.derivedHom` and tensor-Hom adjunction from
  WeilConjectures.SixFunctors.Etale.Derived.Hom. The complete generic ringed-site
  construction is retained; no duplicate derived Hom is introduced.
- WeilConjectures.SixFunctors.Etale.Derived.Tensor: `Etale.derivedTensor`, imported
  transitively by the public derived-category interface, as the proof's K-flat tensor.
- Proof-only imports retain `SheafOfModules.homObj`, `pointedEtaleStalk`,
  `isIso_moduleDualEvaluation_of_retract`, `constantSheaf_sections_locallyConstant`,
  `Functor.homologyFunctorIso`, and `etaleInverseImageModulesExact` in their recorded
  modules. The Galois-refinement, tensor-closure and flat-model proof nodes have no
  recorded Lean statements yet, so there is no proof module to import for them.
  The cover-local-isomorphism node likewise has no recorded module.

Edge cases checked mathematically: X empty uses n=0 with no connected strata;
zero F is allowed and has finite zero stalks; the zero coefficient ring is allowed;
zero N and a=b are included; no hypothesis makes a nonzero rank or positive interval
necessary. FiniteExtensions permits n=0 (only the zero sheaf). The filtered category
is nonempty via IsFiltered, including the constant one-object presentation. Weak
classes have no finite-generation restriction. A may have infinite finitely generated
modules; neither their cardinality nor global finite monodromy is assumed.

Searches (all recorded search calls completed):

- msearch leanfinder: `derived Hom from flat locally constant constructible etale
  sheaf preserves Galois weak constructibility`: 8 hits, condensed local-system
  infrastructure and constructible scheme images; none states this theorem.
- msearch loogle `CategoryTheory.sheafHom`: three generic sheaf-Hom declarations;
  none states the theorem or defines Galois partitions.
- msearch grep `Galois.*[Pp]artition|[Ww]eak.*[Cc]onstructib|[Cc]onstructib.*[Hh]om`:
  six irrelevant constructible-set/partition hits.
- msearch leansearch `finite Galois stratification weakly constructible filtered
  colimit extensions local systems`: eight hits, including abstract Galois objects
  and general filtered colimits, no partition or W_P definition.
- rg of Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for
  `GaloisPartition|ctf_hom_locallyConstant` found no existing declaration.
  The item-id grep in WeilConjectures found none. Broader Hom searches located
  CtfHomCoefficientComparison and EtaleInternalHomDevissage, whose conclusions and
  hypotheses differ. Their source was read.
- DAG definition-node grep found no Galois-partition definition; theorem nodes spell
  it out inline. `tools/blueprint_refs.py search` returned zero for both
  `Galois partition` and `weakly constructible`.

Validation: all three modules compiled separately in dependency order using
`scompile.py`, with no errors or warnings. All universes and binders are explicit;
no local notation, local instance, hidden hypothesis, extra axiom or proof was added.

## New nodes

`def-per-galois-partition-modules`, module `Sheaf.Paper.GaloisPartitionModules`,
packages the notion spelled out in the item's own statement. It extends the recorded
finite locally closed stratification and uses `ConnectedSpace`, `IsReduced`, finite
etale schemes and the existing `PreGaloisCategory.IsGalois`. The latter is equivalent
to the connected geometric-fibre torsor description (`FiniteEtale.isGalois_iff` and
FundamentalGroup.Connected). FiniteExtensions uses a finite chain of actual short exact
sequences, starting at zero and ending at the sheaf. Its quotient sheaves are local
systems with constant pullback. The weak class uses a cocone and its universal
colimit witness; boundedDerived uses the actual derived cohomology. Refines uses the
source's inclusion definition. Source: ILO XVII Definitions 7.3.1--7.3.3. Searches
above establish absence of a competing definition node or existing declaration.
All definitions have real data and contain no sorry.

## Dependency modules

`def-weil-pbc-locally-constant-finite-type-modules`: its original generic predicate
requires category objects and arrows in the same universe and accepts constant-ring
SheafOfModules, whereas the recorded derived-category interface uses ModuleCat-valued
sheaves on an etale site with objects u+1 and arrows u. Section 1(B) repair preserves
its original definition and docstring verbatim and adds only a public import of
WeilConjectures.ConstructibleSheaf.Defs. That established interface supplies the
mathematically equivalent finite-type local system and constructibility predicates
at exactly the ordinary-etale universes; no construction or predicate is copied.
The primary record remains its original definition and lists the exposed existing
specializations in declarations. Both the dependency module and its consumer compile.

## Second reading by Q59

A separate agent was not started, as the dispatch brief explicitly forbids it.
This is a second self-reading; the maintainer supplies the independent review.
With the node and final modules open, I checked the prime, Noetherian and coefficient
binders, local finite-type and exact tensor assumptions, quantifier order P/P'/a/b/N,
weak cohomology classes, unchanged interval, constructibility implication and absence
of a dualizing assumption. I checked every field of the partition, each quotient of
the finite filtration, filteredness and colimit universality. The first draft used
maps between covers for refinement; reading Definition 7.3.3 identified that as too
strong, so it was replaced by ground-field weak-class inclusion before delivery.
Compiler errors in the parent projection name, IsConstant argument order and the
Type-valued IsColimit witness were repaired. No mathematical clause was dropped.
