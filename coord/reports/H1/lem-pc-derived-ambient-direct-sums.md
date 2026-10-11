## Worker report

The module `Sheaf.AlgebraicGeometry.DerivedAmbientDirectSums` states
`AlgebraicGeometry.derivedAmbientDirectSums`, with a sorry proof only. No definitions,
new nodes, dependency modules, or statement corrections are needed.

Hypothesis and clause correspondence:

- Every scheme X: `(X : Scheme.{u})`, with no geometric hypotheses.
- D(O_X): `schemeDerivedCategory X`, using the shared
  `[HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]`.
  This binder supplies the chosen localization, not an extra geometric restriction.
- Every set-indexed family: `(I : Type u) (E : I → schemeDerivedCategory X)`.
  The index is small in the module-sheaf universe, the usual set-indexed coproduct convention;
  u and w are explicit and arbitrary. There is no finite, countable, or nonempty restriction.
- Any representative complexes: `K : I → CochainComplex ... ℤ` and
  `e : ∀ i, DerivedCategory.Q.obj (K i) ≅ E i`. Neither boundedness nor injectivity is imposed.
- Termwise direct sum: `∐ K` in the complex category. Mathlib's
  `HomologicalComplexLimits` computes coproducts degreewise, and supplies preservation by
  each evaluation functor. Its image is `DerivedCategory.Q.obj (∐ K)`.
- Represents a direct sum of the E_i: `Nonempty (IsColimit (Cofan.mk ... ...))`.
  Its legs are `(e i).inv ≫ DerivedCategory.Q.map (Sigma.ι K i)`, so the family in this
  universal property is E itself, not merely the complexes' localization images.
- Every integer q: `∀ q : ℤ`.
- Canonical cohomology isomorphism: `IsIso (Sigma.desc ...)`. The map goes from
  `∐ (fun i ↦ (DerivedCategory.homologyFunctor ... q).obj (E i))` to
  `(DerivedCategory.homologyFunctor ... q).obj (DerivedCategory.Q.obj (∐ K))`.
  Its component on each summand is the cohomology of the very same derived coprojection.
  IsIso asserts the canonical map is invertible, hence gives the stated canonical
  isomorphism (in the inverse orientation to the prose if desired), not an arbitrary
  existence of an isomorphism.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, the locally affine
  locally ringed space definition, and its morphisms.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `AlgebraicGeometry.schemeDerivedCategory`,
  the abbreviation for the DerivedCategory of the shared SheafOfModules carrier.
  Read all three recorded definitions, including schemeDerivedQCohProperty and
  schemeDerivedQCohCategory; the latter two concern a restriction not present in this item.
- Its shared `moduleRings` abbreviation was read in
  `Sheaf.Paper.DerivedHomMayerVietoris`; it composes the structure sheaf with forgetting
  commutative rings to rings.
- Mathlib `DerivedCategory.Q` and `DerivedCategory.homologyFunctor` (and its factoring
  isomorphism) supply localization and cohomology. Mathlib's sheaf colimits and
  HomologicalComplexLimits supply the ambient and termwise coproducts.

Edge cases: I may be empty, so the statement includes the initial/zero coproduct;
I may be singleton; the complexes may all be zero; q may be negative or zero; X may
be empty. No binder excludes these. No Noetherian, separatedness, or quasi-coherence
assumption is present. The representative isomorphisms merely express the word
'representatives' and leave every possible representative available.

Sources opened: https://stacks.math.columbia.edu/tag/07D9, clauses (1)-(2), and
https://stacks.math.columbia.edu/tag/08DT, its proof. They state the termwise construction
and exact-sum cohomology identity for the ambient derived category. The theorem's
docstring includes all three DAG proof steps and the K-injective universal-property
argument from 07D9. The repository's literature/stacks-project source files are absent
on this machine, so the source tags were read online.

Searches for an existing statement:

- msearch leanfinder: "derived category of sheaves of modules coproduct represented by
  termwise direct sums and cohomology commutes with coproducts". Eight hits, including
  SheafOfModules.isColimitFreeCofan, Sheaf.cohomologyPresheafFunctor, Sheaf.H,
  Sheaf.cohomologyPresheaf, SheafOfModules.mapFree, Grothendieck-category instances,
  and SheafOfModules.instAbelian. None states this derived coproduct/cohomology result.
- msearch loogle: "DerivedCategory.Q, PreservesColimitsOfShape". Zero hits;
  the service reported unknown identifier PreservesColimitsOfShape.
- msearch leansearch: "derived category coproduct cohomology direct sums".
  Service unavailable (Internal Server Error), recorded as unavailable.
- msearch grep: "coproduct|Coproduct|PreservesColimit" in Algebra/Homology/DerivedCategory:
  zero hits. Direct rg of the same directory agrees.
- rg of WeilConjectures for derived/coproduct/direct-sum names and the item id: no exact
  statement; rg of DirectImage.lean for coproduct/direct sums has no hit.
- rg of lean/Sheaf found CategoryTheory.derivedModuleDirectSums in
  Sheaf.CategoryTheory.DerivedModuleDirectSums. Read it in full: it concerns modules
  over a ring, not sheaves over a scheme, and lacks the cohomology clause, so is not this node.
- Read Mathlib HomologicalComplexLimits, DerivedCategory.HomologySequence, and
  Limits.Shapes.Products for the existing degreewise coproduct infrastructure,
  homology functor, and canonical Sigma.desc map; no copied notions were introduced.

Validation: scompile.py compiled the 50-line module on the server in 2.9 seconds,
with exit code 0 and no warnings. All variables and universes are explicitly bound.
No STATEMENT-DISPUTED or node fault was found.


## Second reading by H1

I independently read the node, the delivered module, both statement dependency nodes
and their actual Lean declarations. I also read Mathlib's Scheme, DerivedCategory.Q,
homologyFunctor and homologyFunctorFactors, HomologicalComplexLimits, SheafOfModules
colimit instances, and Sigma.desc. There are no new nodes, dependency modules, or
statement corrections in this delivery.

The source .tex is absent locally. I read the Stacks pages 07D9 and 08DT and fetched
and read the corresponding lemma/proof environments in the upstream injectives.tex
and perfect.tex at https://raw.githubusercontent.com/stacks/stacks-project/master/.
07D9 assumes a Grothendieck abelian category; 08DT assumes only a scheme. Its proof
establishes the ambient cohomology identity before invoking quasi-coherence, so
quasi-coherence is not a hypothesis of this item.

Object/hypothesis/conclusion checklist, in the node's order:

1. Every scheme X: `(X : Scheme.{u})`. Mathlib Scheme extends a locally ringed space
   with local affine charts. Verdict: the dependency's scheme, no extra geometric
   property or base field.
2. The ambient D(O_X): `schemeDerivedCategory X` from the recorded dependency module,
   which unfolds to DerivedCategory of `SheafOfModules.{u} (moduleRings
   X.toRingedSpace)`. I read moduleRings: it forgets the commutative-ring structure
   of the structure sheaf. The Abelian instance is the shared Mathlib instance.
   `[HasDerivedCategory.{w} ...]` chooses the localization and its morphism universe;
   the standard localization exists, so this is not a finiteness hypothesis.
   Verdict: the ambient category, not D_QCoh, X.Modules with another instance,
   abelian sheaves, or modules over a single global ring.
3. Every set-indexed family of derived objects: `(I : Type u)
   (E : I → schemeDerivedCategory X)`. Verdict: arbitrary small sets in the
   module-carrier universe, no Fintype, Countable, or Nonempty restriction.
   The module universe u is arbitrary, so this is the standard universe-relative
   set-indexed convention; it does not claim sums larger than the sheaf carriers.
4. Any representative complexes: `K : I → CochainComplex ... ℤ` and
   `e : ∀ i : I, DerivedCategory.Q.obj (K i) ≅ E i`. Verdict: all integer-indexed,
   possibly unbounded representatives; e identifies the representative with the
   actual E, not an additional mathematical restriction on E. Q is the recorded
   localization at quasi-isomorphisms, not a bounded derived functor.
5. Termwise sum represents a direct sum of E: `Nonempty (IsColimit (Cofan.mk
   (DerivedCategory.Q.obj (∐ K)) (fun i ↦ (e i).inv ≫
   DerivedCategory.Q.map (Sigma.ι K i))))`. Verdict: the full coproduct universal
   property of E itself. Mathlib's complex colimits are computed degreewise,
   as confirmed by coconeOfHasColimitEval and the evaluation-preservation instance.
   Each leg starts at E i, goes to Q(K i), then to Q(∐ K).
6. Every integer q: `∀ q : ℤ`, after the universal-property conjunct.
   Verdict: quantifier order and all degrees match.
7. Canonical cohomology isomorphism: `IsIso (Sigma.desc (fun i ↦
   (DerivedCategory.homologyFunctor ... q).map
   ((e i).inv ≫ DerivedCategory.Q.map (Sigma.ι K i))))`.
   Verdict: the map has source ∐ H^q(E i) and target H^q(Q(∐ K)); its restriction
   to each summand is precisely cohomology of the same coprojection. IsIso gives
   invertibility of this canonical map, equivalent to the node's isomorphism
   with the opposite orientation. homologyFunctorFactors identifies this functor
   with cochain cohomology, so it is sheaf cohomology in the complex degree,
   not global-section cohomology. No arbitrary isomorphism weakens canonicity.

Edge cases: an empty I gives a zero/initial complex coproduct and includes its
universal property and the zero cohomology comparison. Singleton families and
zero complexes are included. The empty scheme is allowed by Scheme with no
extra property; q = 0 and all negative degrees are included by ℤ. No assumption
on characteristic, separatedness, Noetherianity, boundedness or quasi-coherence
appears. u and w are explicitly bound; the index universe agrees with the
sheaf module universe, and w is independent for localization morphisms.

Independent searches (different wording from the worker):

- msearch leanfinder: "localization of cochain complexes preserves arbitrary small
  coproducts and homology preserves coproducts". Eight hits: localization instances,
  homologyFunctor and its homological instance, complex Grothendieck structure,
  and t-structure/Ext facts. None gives this coproduct/cohomology statement.
- msearch loogle: `"DerivedCategory", "colimit"`. Zero hits.
- msearch leansearch: "cohomology of arbitrary coproduct of complexes of module
  sheaves in derived category". Service unavailable (Internal Server Error),
  explicitly recorded as unavailable, not evidence of absence.
- rg of Mathlib DerivedCategory/, Localization.lean, and CategoryTheory/Localization
  for coproduct/Coproduct/directSum/preservesColimit: no relevant declaration.
  The complex GrothendieckAbelian file gives stability of quasi-isomorphisms under
  coproducts, not this derived universal property or its cohomology conclusion.
- rg of the whole WeilConjectures and lean/Sheaf for derived sums/coproducts:
  no exact statement. I opened CategoryTheory.derivedModuleDirectSums in full;
  its carrier is ModuleCat R, not O_X-module sheaves, and it has no canonical
  cohomology clause. The site-specific direct-image preservation results also
  do not state this ambient coproduct theorem. No existing declaration to reuse.

Mismatch and repair: the last proof-docstring sentence said "maps to E i" although
all coprojections start at E i. Changed it to "coprojections from E i". The Lean
signature and node lean.statement are unchanged and equal verbatim (up to the
project's whitespace normalization). No mathematical mismatch was found.
The docstring otherwise supplies all three node proof steps and the source's
K-injective argument. The only theorem proof is sorry; there are no definitions
or private notions, no unbound variable/universe, and lines respect the conventions.

Validation after the docstring repair: scompile.py compiled the 50-line module
in 2.8 seconds, exit 0, with no warnings. I also compared the node signature
verbatim with the file and checked all line lengths are at most 100.
