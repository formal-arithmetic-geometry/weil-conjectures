## Worker report

The item is stated in `Sheaf.AlgebraicGeometry.DiscreteNoetherianConstructibleSerre` by
`AlgebraicGeometry.etale_discreteNoetherian_constructible_serre` and
`AlgebraicGeometry.proEtale_discreteNoetherian_constructible_serre`. Both proofs are `sorry`;
there are no other postponed proofs in this delivery. Their docstrings give all six steps
of the DAG proof. No source statement was corrected and no disputed assertion was found.

The new definition module is
`Sheaf.AlgebraicGeometry.AffineLocallyConstructibleProEtaleModules`, owned by the new node
`def-sfb-affine-locally-constructible-proetale-modules`. Its definition has real data: the
explicit affine-open, stratification, covering-sieve, module and isomorphism quantifiers.
The item also gains the already landed `def-pe-etale-constructible-module` as a statement
dependency so that it reuses the existing arbitrary-Noetherian etale notion.

Hypothesis and clause correspondence:

- Scheme: `(X : Scheme.{u})`, with no Noetherian, quasi-compact, separated, or finite-type
  assumption on X, in both theorems and the new definition.
- Commutative discrete Noetherian coefficients: `(R : Type ...) [CommRing R]
  [IsNoetherianRing R]`. Constant sheafification gives the discrete-coefficient meaning;
  there is no `TopologicalSpace R`, `Finite R`, torsion, characteristic, or invertibility
  assumption. The etale theorem uses R in Type (u+1), as the landed etale interface does.
  The pro-etale theorem uses R in Type u and its canonical `ULift.{u+1,u} R`, as the
  recorded intrinsic module and inverse-image interfaces do. Site objects remain in
  Type (u+1) and morphisms in Type u; no equality of those site universes is imposed.
- Small etale site: `X.smallEtaleTopology`; small pro-etale site: `Scheme.ProEt.topology X`.
- Ambient module categories: `ringedSiteModules.{u+1}` over
  `(constantSheaf X.smallEtaleTopology RingCat.{u+1}).obj (RingCat.of R)` for etale;
  `Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X R)` for pro-etale.
  The latter is exactly `SheafOfModules` over the underlying ring of the constant
  commutative ring sheaf, not a continuous-function or finite-coefficient replacement.
- Affine-local constructibility on the etale site:
  `Etale.constructibleNoetherianModules X R`, from the landed etale definition, applies
  `Scheme.IsAffineLocallyConstructibleEtaleModuleSheaf` after the canonical
  `Scheme.etaleConstantModuleRestrictionFunctor`. This functor restricts to constant
  scalars and is the inverse of the canonical extension of the scalar action. It keeps
  the abelian sheaf and its linear maps, so it expresses precisely modules over the
  constant ring sheaf. The underlying predicate begins
  `∀ U : X.Opens, IsAffineOpen U → ∃ S : Scheme.LocallyClosedStratification U.toScheme`.
- Affine-local constructibility on the pro-etale site: the new
  `Scheme.IsAffineLocallyConstructibleProEtaleModuleSheaf X R` begins with exactly the
  same affine-open and stratification quantifiers.
- Finite, pairwise disjoint, covering, locally closed parts and their scheme immersions
  come from the recorded `Scheme.LocallyClosedStratification`, including `S.n`,
  `S.domain`, `S.stratum`, `S.immersion`, `S.isImmersion`, and `S.range_immersion`.
  Both predicates explicitly test `Topology.IsConstructible (S.stratum a)` in U, as the
  existing etale predicate does. This agrees with the current upstream stratification
  API even where constructibility is already an inherited field; no new condition is
  imposed on the partition. No positive lower bound on `S.n` is added.
- Restriction to a stratum of U uses the composite `S.immersion a ≫ U.ι`. On the etale
  side it is `Etale.upperStar (ModuleCat R)` on the constant-scalar presentation. On the
  pro-etale side it is the recorded `Scheme.proEtaleConstantModulePullback`, which is
  module inverse image followed by tensor extension along the canonical coefficient
  structure map. A closed stratum is not treated as an object of the ambient site.
- Local constancy with finitely presented coefficient-module values on the pro-etale
  side is expressed directly: for every V in the stratum site choose a covering sieve T;
  every `f : W ⟶ V` in T has `M : ModuleCat.{u+1} (ULift R)`,
  `Module.FinitePresentation (ULift R) M`, and
  `Nonempty ((proEtaleConstantModulePullback ...).over W ≅
    proEtaleConstantModuleSheafOver ... W M)`.
  These are isomorphisms of module sheaves over the same localized coefficient sheaf.
- On the etale side the existing predicate uses a trivializing etale covering and
  finitely generated constant module models. This is the same predicate under the
  stated Noetherian hypothesis: a finitely presented module is finite by the instance
  following `Module.FinitePresentation`; conversely
  `Module.finitePresentation_of_finite R M` gives finite presentation. Covers of the
  terminal site object and covering sieves over every object give the same local
  condition by pulling back the cover. This is the finiteness conversion explicitly
  required by step 1 of the item, not an added hypothesis or a changed definition.
- Contains zero: the first conjunct of each theorem applies its predicate to the
  ambient zero object (`open scoped ZeroObject`, the standard Mathlib scope).
- Kernels and cokernels: the second conjunct quantifies over every F, G and ambient
  morphism `f : F ⟶ G`; the two constructibility antecedents imply constructibility of
  both `kernel f` and `cokernel f`. Neither mono nor epi is assumed.
- Extensions: the third conjunct quantifies over every ambient `ShortComplex S`;
  `S.ShortExact`, constructibility of `S.X₁`, and constructibility of `S.X₃` imply
  constructibility of `S.X₂`. ShortExact includes injectivity, middle exactness, and
  surjectivity, hence exactly the displayed sequence with zeros at the ends.
- Weak Serre means precisely those displayed clauses here; no stronger subobject or
  quotient closure condition is substituted.

Dependency declarations read and used (the recorded modules are imported directly or
reexported through the imports defining the objects):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`, `Scheme.Etale`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: `Scheme.proEtaleDerivedCategory`,
  whose category expression fixes the intrinsic constant-ring coefficient convention;
  its public site is Mathlib's `Scheme.ProEt` and `Scheme.ProEt.topology`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.AlgebraicGeometry.LocallyClosedStratification`:
  `Scheme.LocallyClosedStratification`, reusing `Topology.Stratification`.
- `Mathlib.Algebra.Module.FinitePresentation`: `Module.FinitePresentation`, its finite
  instance, and `Module.finitePresentation_of_finite` (the last is a proof dependency).
- `Mathlib.Topology.Constructible`: `Topology.IsConstructible`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar` and its
  recorded adjunction, applied by the landed etale constructibility predicate.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`: the recorded inverse-image
  dependency module. Its primary `sfIntrinsicConstantModuleAdjunction` has finite
  coefficients and is not applied here. It publicly reexports the usable arbitrary-ring
  `Sheaf.AlgebraicGeometry.ProEtaleInverseImage` constructions, including
  `Scheme.proEtaleConstantRing` and `Scheme.proEtaleConstantModulePullback`, which are
  the ones used. No finite-coefficient adjunction is generalized or assumed.
- `Sheaf.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf`:
  `SheafOfModules.IsFiniteTypeLocallyConstant`; imported as the recorded small-site
  local notion for the proof. The explicit finitely presented model clause of the
  new stratified predicate does not introduce a second generic local-constancy API.
- `Sheaf.AlgebraicGeometry.ConstructibleNoetherianEtaleModules`:
  `Etale.constructibleNoetherianModules`, `Scheme.IsAffineLocallyConstructibleEtaleModuleSheaf`.
- `Sheaf.AlgebraicGeometry.EtaleConstantRingModuleEquivalence`:
  `Scheme.etaleConstantModuleRestrictionFunctor`, the canonical scalar restriction.
- `Sheaf.AlgebraicGeometry.ProEtaleOperations`: `Scheme.proEtaleRingModules`, a transparent
  ambient-category abbreviation.
- `Sheaf.Paper.ProEtaleLocallyConstantSheaf`:
  `Scheme.proEtaleConstantModuleSheafOver`, the already constructed localized constants.

All recorded proof-dependency modules are retained as ordinary imports (or are already
public statement imports). These include etale algebraic-structure inverse image,
`siteInverseImage_tensor`, `sitePullback_abelian_exact`, `Scheme.Stratification.inter`,
`siteMorphism_composition`, `localize_ringed_site_morphism`, the generic finite-type
locally-constant Serre theorem, the Noetherian finite-presentation theorem, and the
Mathlib etale-cover base-change interface. The two upstream modules absent from the
older local source tree were read using `scompile.py --source` with their exact recorded
module names. No dependency module or record-only repair was necessary.

Edge cases checked against the definitions and source:

- Empty X and empty affine U are admitted; `S.n = 0` is allowed when the union condition
  can hold, and an identity empty stratum is also allowed. Covering sieves may be empty
  on site objects for which the topology permits them.
- The zero ring is allowed (`CommRing` does not require Nontrivial); all its modules are
  zero, and there is no excluded characteristic or invertibility assumption.
- R = Z, and maps such as Z to Z/2, are covered: finite generation means module finite
  generation, not finiteness of the underlying coefficient or module sets.
- Zero objects, zero morphisms, non-mono/non-epi maps, split extensions, and extensions
  with either outer object zero are included by the unrestricted categorical binders.
- Noetherianity belongs to R, not to the scheme. A non-quasi-compact X requires only one
  finite partition for each affine open, not one global finite partition.
- Closed stratum restrictions use inverse image of sites with the specified coefficient
  map, and local models use the localized ringed sites, not the small site of an assumed
  open subobject. The common-refinement proof uses actual fibre-product strata.

Searches performed:

- `msearch.py` LeanFinder: “Constructible sheaves of modules over a discrete Noetherian
  ring on the etale and pro etale sites closed under kernels cokernels and extensions”.
  Eight hits: CondensedMod, its abelian/AB5 and light variants, solid modules, and
  condensed locally constant functors. None states this scheme-site theorem.
- `msearch.py` Loogle: `"Sheaf", "Serre"` returned zero hits.
- `msearch.py` grep: `constructib.*[Ss]erre|[Ss]erre.*constructib` returned zero hits.
- `msearch.py` LeanSearch: “Affine locally constructible pro etale sheaves of modules
  over a noetherian ring” returned general Scheme.Modules/SheafOfModules constructors,
  generators data and scheme Noetherian/etale results, not this predicate.
- `msearch.py` LeanFinder for the new definition's full affine-local description returned
  SheafOfModules.IsFiniteType/IsFinitePresentation and related local presentation APIs;
  none includes stratifications or locally constant coefficient-module models.
- `msearch.py` grep:
  `AffineLocallyConstructible|[Cc]onstructible.*[Pp]ro[Ee]tale|[Pp]ro[Ee]tale.*[Cc]onstructible`
  returned zero Mathlib hits.
- `rg` of the upstream WeilConjectures tree, project lean/Sheaf tree and
  dag/lean_names_upstream.json found only finite-coefficient/global pro-etale
  constructibility and the exact reusable etale affine-local predicate.
  The item-id search of WeilConjectures returned no match. Existing constructible
  Serre statements require finite coefficient sets, and cannot replace this one.
- `tools/blueprint_refs.py search 'constructible proetale'` returned zero blueprint
  matches. Broader constructible and DAG searches distinguished the finite/global and
  condensed notions from the new affine-local discrete Noetherian pro-etale notion.

Validation: both delivered modules compiled individually, including under their library
module names, through `scompile.py` in dependency order with the prescribed 60-second
limit. The last runs took about 1.5 seconds for the definition and 2.4 seconds for the
statement, with no warnings. Auto-implicit variables are disabled explicitly. No global
build or direct compiler command was used. The two theorem bodies are exactly `by sorry`;
the new definition contains no postponed proof.

## New nodes

`def-sfb-affine-locally-constructible-proetale-modules` defines exactly the missing
intrinsic pro-etale affine-local constructibility predicate for an arbitrary discrete
commutative Noetherian ring, with finitely presented constant module models on localized
sites. Its source is Stacks 09AJ (definition-constructible), with 00IK converting finite
type to finite presentation. Search results are recorded on the new node. Existing
`def-weil-proetale-constructible-sheaf` is finite-coefficient and globally stratified;
`def-sfb-constructible-module` concerns condensed coefficients; the landed
`def-pe-etale-constructible-module` concerns the etale site and is reused for that half.
The new module reuses the existing strata, coefficient sheaves, intrinsic module
pullback and localized constant-module construction; none of those notions is copied.
The ancestor returned by `blueprint_refs.py ancestor` is
`det-lem-integral-models-stacks`, and the new node's provenance records the discrete
Noetherian closure input served here.

## Second reading by Q129

I independently read the item node and both sandbox modules, the new definition node,
and Stacks proetale.tex, definition-constructible (09AJ) and lemma-constructible-serre
(09B5), together with etale-cohomology.tex, definition-constructible (03RW, clause 3)
and lemma-constructible-abelian (03RZ, clause 3 and its proof). Those source passages
assume an arbitrary scheme and a Noetherian coefficient ring; they impose no
Noetherianity, quasi-compactness, separatedness, finite characteristic, torsion, or
invertibility condition on X. The sources use finite-type module values, which agree
with the node's finitely presented values over this coefficient ring.

My object/hypothesis/conclusion checklist, with the Lean rendering and verdict:

1. An arbitrary scheme X: `(X : Scheme.{u})` in both theorems and the new definition.
   This is Mathlib's Scheme, with no extra scheme-property instance. Exact.
2. A discrete commutative Noetherian R: `[CommRing R] [IsNoetherianRing R]`.
   No topological ring structure or `[Finite R]` is required. Discreteness is encoded
   by the constant sheaf, rather than a sheaf of continuous functions. Exact.
3. Either small site: `X.smallEtaleTopology` and `Scheme.ProEt.topology X`.
   I opened the Mathlib site declarations: Etale consists of etale X-schemes;
   ProEt consists of weakly etale X-schemes with the fpqc topology. Exact.
4. All modules over the constant ring sheaf, with all linear morphisms:
   `ringedSiteModules.{u+1} ((constantSheaf ... RingCat.{u+1}).obj (RingCat.of R))`
   and `Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X R)`.
   I opened RingedSiteModules, ProEtaleOperations, ProEtaleDerivedCategory and
   ProEtaleInverseImage. These transparently use Mathlib SheafOfModules over the
   sheafified constant ring; the pro-etale coefficients use the canonical ULift.
   No ambient full-subcategory restriction is hidden here. Exact.
5. For every affine open, a possibly different finite partition:
   both predicates begin `∀ U : X.Opens, IsAffineOpen U → ∃ S :
   Scheme.LocallyClosedStratification U.toScheme, ...`. This does not replace
   affine-local constructibility by a global stratification. Exact.
6. The parts are pairwise disjoint, cover U, are locally closed and constructible
   in U, and have scheme immersions: `S.n`, `S.stratum`, inherited
   `isLocallyClosed_stratum`, `pairwise_disjoint_stratum`,
   `iUnion_stratum_eq_univ`, `S.domain`, `S.immersion`, `S.isImmersion`, and
   `S.range_immersion`. I opened LocallyClosedStratification and the imported
   Topology.Stratification. The current upstream latter already carries
   constructibility; the explicit `∀ a, Topology.IsConstructible (S.stratum a)`
   repeats that same required condition without strengthening this node. Exact.
7. Inverse image along each stratum's composite map to X:
   `Etale.upperStar ... (S.immersion a ≫ U.ι)` and
   `proEtaleConstantModulePullback (S.immersion a ≫ U.ι) R F`.
   I opened the recorded upperStar definition and the arbitrary-ring pro-etale
   pullback, its coefficient map, and its module inverse-image construction.
   The latter tensors along the adjoint of the canonical constant-section map.
   There is no assumption that a closed stratum is an ambient site object. Exact.
8. Local constant, finitely presented module values:
   the pro-etale definition quantifies over every V, chooses a covering sieve T,
   and for each `f : W ⟶ V` in T chooses `M`,
   `Module.FinitePresentation (ULift R) M`, and
   `Nonempty ((proEtaleConstantModulePullback ...).over W ≅
   proEtaleConstantModuleSheafOver ... W M)`. I opened the localized constant
   construction: its ring is precisely the restricted constant ring, and its
   data is simultaneous constant-ring/module sheafification. The etale predicate
   instead uses an etale covering of the stratum, `Module.Finite R M`, and
   constant ModuleCat-valued sheaves after the existing constant-scalar
   restriction functor. I opened both that predicate and its restriction/extension
   equivalence. It retains the underlying abelian sheaf and module morphisms.
   A covering of the terminal object pulls back to coverings of all objects;
   conversely the all-objects condition applies to the terminal object. Finite
   presentation implies Module.Finite by the Mathlib instance immediately after
   the definition; `Module.finitePresentation_of_finite` proves the converse
   over Noetherian R (both declarations opened). These are equivalent expressions
   of the node's local condition. Exact under precisely the stated hypothesis.
9. Zero belongs to the constructible class: first conjunct, predicate applied to
   `(0 : <ambient category>)`, separately on both sites. Exact.
10. Every morphism between two constructible objects has constructible kernel AND
    cokernel: second conjunct, `∀ F G ... (f : F ⟶ G), P F → P G →
    P (kernel f) ∧ P (cokernel f)`. No mono, epi or nonzero hypothesis occurs. Exact.
11. Extensions: third conjunct, `∀ S : ShortComplex ..., S.ShortExact →
    P S.X₁ → P S.X₃ → P S.X₂`. I opened Mathlib's ShortExact: it means middle
    exactness together with a mono first map and epi second map, hence exactly
    the displayed short exact sequence with zeros at its ends. Exact.
12. The meaning of weak Serre is the displayed zero/kernel/cokernel/extension
    clauses. Both statements spell them out and add no subobject-closure clause.
    Exact. Splitting the two choices of site into two theorems loses no case.

Dependency and new-node audit: all statement-dependency records were read alongside
their signatures. In particular, the primary `sfIntrinsicConstantModuleAdjunction`
in the current inverse-image record requires finite coefficients, but it is NOT
applied in either statement or the new definition. The same recorded module publicly
reexports the arbitrary-ring ProEtaleInverseImage constructions actually used here;
I checked their signatures and bodies. Thus no extra coefficient finiteness enters.
The generic `SheafOfModules.IsFiniteTypeLocallyConstant` is on a small category;
it supplies the local proof input after small-model transport, not a replacement
for the canonical stratum pullback. The new node adds only the absent affine-local
stratified predicate, built out of existing objects. Its TeX statement matches its
definition clause by clause, and follows 09AJ plus the 00IK finiteness conversion.
Its id, chapter/unit, cited stmt_deps, empty proof fields, null mathlib_match,
created/blueprint provenance, lean_audit and lean record meet §5. There are no
dependency modules or statement corrections in this delivery, so no citer audit
under §1(C) is required.

Edge cases: empty X and empty affine U are allowed; `Fin S.n` permits n = 0,
and the covering/union requirement only permits an empty partition where appropriate.
No positivity requirement on n occurs. Empty covering sieves are admitted exactly
when the topology admits them. The zero ring is allowed by CommRing; zero modules,
zero maps, split extensions and extensions with zero outer terms are included.
R = Z and module maps Z → Z/2 are covered: module finiteness is not set finiteness.
There is no characteristic restriction. Non-quasi-compact X still only requires a
finite partition on each affine open. The etale convention uses scalars and modules
in u+1; the pro-etale convention uses R in u, its ring-equivalent ULift in u+1,
and modules in u+1, as the recorded dependency interfaces do. Neither theorem
identifies site object universe u+1 with morphism universe u. All universe parameters
and variables in both files are explicitly bound, with autoImplicit false.

Independent searches (different queries from the first worker):

- LeanFinder via msearch: "Finite stratification locally constant finitely presented
  modules on scheme sites kernel cokernel extension closure". Eight hits concerned
  local finite presentation and quasi-coherent presentations of module sheaves;
  none supplies this stratified coefficient predicate or its two-site closure theorem.
- Loogle via msearch: `"constructible"`. Its hits were constructible subsets and
  their topological operations, not constructible coefficient sheaves or Serre closure.
- LeanSearch via msearch: "Locally constant coefficient modules on affine locally
  closed proetale strata". Eight hits included LocallyConstant modules, the profinite
  Nobeling theorem, tilde sections and condensed discrete modules; none is this notion.
- Independent rg over Mathlib, upstream WeilConjectures and project lean/Sheaf:
  `constructible.*[Ss]erre|[Ss]erre.*constructible|AffineLocallyConstructible|IsConstructibleProEtale`.
  I opened the relevant hits: the existing pro-etale predicates require finite rings
  and a global partition, while the arbitrary-Noetherian affine-local predicate is
  the already reused etale one. Upstream IsConstructibleSheaf kernels/cokernels
  use its global stratification notion, and its extension theorem requires Finite
  coefficients, so they do not jointly state this item. Searches of the upstream
  name index and source tree for this item's id and all three proposed declaration
  names found no declaration collision. The generic local finite-type predicate is
  reused as a proof dependency; no duplicate generic local predicate is introduced.

Mismatch findings and changes: none in the Lean statements, new definition or node
records. I left them unchanged and appended this independent reading only. Both
docstrings contain the source/blueprint tags and all six proof steps, with their DAG
inputs. The only theorem bodies are the two `by sorry` bodies; the new definition
contains real quantifiers and constructions and no postponed data. Both lean.statement
records were compared verbatim with the corresponding file signatures.

Validation: the prescribed scompile.py compiled both sibling files separately, in
dependency order, and checked their library-module names. The definition compiled in
1.5 seconds and the statement in 2.4 seconds, with no errors or warnings. No live
source was edited and no global build was run.
