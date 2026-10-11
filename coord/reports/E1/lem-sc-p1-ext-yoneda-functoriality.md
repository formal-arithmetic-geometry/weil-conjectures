## Worker report

The module `Sheaf.AlgebraicGeometry.Modules.ExtYonedaFunctoriality` states
`AlgebraicGeometry.Scheme.Modules.ext_yoneda_functoriality`, with its proof `sorry`.
No statement correction or new node is needed.

Hypotheses and clauses matched:
- A scheme X: `{X : Scheme.{u₁}}`; arbitrary universe, no finiteness or base hypothesis.
- The recorded Ext groups: `Scheme.Modules.Ext`, with `[HasExt.{u₁} X.Modules]`, the
  infrastructure argument of the recorded definition (available for all scheme modules).
- Four O_X-modules: `(F F' G G' : X.Modules)`.
- i >= 0 and an Ext class: `(i : ℕ) (e : Ext F G i)`.
- u : F' -> F and phi : G -> G': `(u : F' ⟶ F) (φ : G ⟶ G')`.
- Contravariant Ext map equals e composed with u: the first conjunct applies
  `((Abelian.extFunctor i).map u.op).app G` to e and equates it with
  `(Abelian.Ext.mk₀ u).comp e (zero_add i)`.
- Covariant Ext map equals phi[i] composed with e: the second conjunct applies
  `(Abelian.extFunctorObj F i).map φ` and equates it with
  `e.comp (Abelian.Ext.mk₀ φ) (add_zero i)`.
- Naturality of the canonical Ext(O_X,G) = H(i,G) identification: the third conjunct
  quantifies over every `a : Ext (SheafOfModules.unit X.ringCatSheaf) G i` and says
  `unitExtModuleAddEquiv` carries the covariant Ext map to
  `(RingedSpace.moduleCohomology X.toRingedSpace i).map φ`.
- The last formula for every cohomology class x: the fourth conjunct quantifies over
  the carrier of `(moduleCohomology X.toRingedSpace i).obj G`, applies the inverse
  canonical comparison, composes with `mk₀ φ`, and transports forward. Thus the
  notation phi[i] composed with x is interpreted under the specified identification.

Dependency declarations read and used:
- `WeilConjectures.AlgebraicGeometry.Modules.Ext`, `Scheme.Modules.Ext` (abbreviation
  of `Abelian.Ext`; its upstream docstring's contravariant wording was already corrected
  by the DAG, while its actual definition is the correct derived-category Ext).
- `Sheaf.AlgebraicGeometry.Modules.ExtYonedaAssociativity`,
  `Scheme.Modules.ext_yoneda_assoc_pushout`, and its `Abelian.Ext.comp` operation.
  The imported theorem is for the proof stage; it adds no hypotheses to this statement.
- `Sheaf.AlgebraicGeometry.LocallyFreeExtCohomology`,
  `locallyFreeExtAddEquivH`, `locallyFreeUnitExtAddEquivH`, and
  `isIso_dualTensorHom_of_isFiniteLocallyFree`. The first two target the other encoding
  of cohomology, so the dependency module described below supplies the needed comparison.
- `Sheaf.Topology.RingedSpaceModuleCohomology`, `RingedSpace.moduleCohomology`,
  `RingedSpace.globalSectionsFunctor`, and `RingedSpace.globalSectionsComplex`.
- Mathlib `Abelian.extFunctor`, `Abelian.extFunctorObj`, `Abelian.Ext.mk₀`,
  `Abelian.Ext.comp`, `InjectiveResolution.extMk`, and `isoRightDerivedObj`.

Edge cases checked mathematically: i=0 gives ordinary pre/postcomposition and the
Hom(O_X,G)=Gamma(G) comparison; identity maps give identity actions; zero maps/classes
are sent to zero. The empty scheme and zero modules are allowed. The dependency uses
finite locally free modules of varying finite local rank, including rank zero, with no
fixed-rank assumption. It specializes to O_X on every scheme, with no properness,
Noetherian, separatedness, or base-field condition. No unbound variables or local
notation/instances occur in statements. Definitions use explicit instance lets only
where they construct data.

Searches (logged by msearch.py in searches.jsonl):
- LeanFinder: "Ext functoriality is Yoneda composition and Ext of structure sheaf
  cohomology identification is natural" returned extFunctor_map_app, the derived
  degree-zero composition lemmas and abelian-sheaf cohomology declarations, but no
  scheme-module canonical comparison naturality statement.
- Loogle: "CategoryTheory.Abelian.Ext.mk₀, CategoryTheory.Abelian.Ext.comp" returned
  mk₀ composition formulas and extFunctor_map_app; no full statement.
- LeanSearch: "Ext from a tensor unit is naturally isomorphic to right derived global
  sections" was unavailable (Internal Server Error); no verdict for this search.
- Mathlib grep for `extFunctor|mk₀_comp|comp_mk₀` in
  Algebra/Homology/DerivedCategory/Ext found the usual Ext functor/composition API.
  The initial grep in CategoryTheory/Abelian/Ext had no hits (wrong subtree); the
  subsequent search used the correct subtree.
- Source and project rg for `locallyFreeUnitExt|ext_yoneda_functor|extFunctor|ext_addEquiv_H`
  found only the existing comparison declarations described above. Grep of the source
  for the item id found nothing. Rg for the proposed full declaration names found no
  collisions. Additional searches for Ext/moduleCohomology found no existing bridge.

Sources read: Stacks 06XP (https://stacks.math.columbia.edu/tag/06XP) defines Ext as
Hom in the derived category and describes injective resolutions and Yoneda composition;
01DZ (https://stacks.math.columbia.edu/tag/01DZ) supplies derived global-sections
functoriality. The dependency node's full statement and five-step proof were read;
its local blueprint source is absent on this machine, and a fetch of the recorded
blueprint path at the recorded master commit returned 404.

## Dependency modules

`lem-sc-ext-locally-free`: `LocallyFreeExtModuleCohomology.lean` states the full comparison
for every finite locally free F, every G, and every natural degree i, with target
`moduleCohomology` of F-dual tensor G. The old recorded declaration targets `G.H`,
cohomology of the underlying abelian sheaf; there is no recorded natural bridge to the
module-cohomology functor. The old declarations remain imported and reused, including
inverse evaluation. The new existence theorem characterizes the equivalence on
`I.extMk f` for every injective resolution I of G, every resolution J of F-dual tensor G,
and every lift from tensor(I) to J: its image is the cohomology class of the inverse
evaluation section transported through J. This characterization determines the
canonical equivalence independently of all choices. `locallyFreeExtModuleAddEquiv`
chooses that characterized equivalence; `unitExtModuleAddEquiv` specializes to the unit
and applies the canonical dual-unit evaluation and left unitor through moduleCohomology.
Neither definition has missing data. The named existence theorem has `sorry` with a
complete proof docstring and belongs to this dependency node. The dependency JSON
changes only its lean record, whose note explains the encoding mismatch.

Validation: both modules were compiled together on the server. The final delivery dry run
also checks the node records, declaration docstrings, sorry-only proofs, and line widths.


## Second reading by E1

Independent review of the item node and both delivered modules. Verdict: the Lean
states the node, using the recorded Ext and module-cohomology notions; no statement
correction or new definition node is required.

Objects, hypotheses, and conclusion clauses, matched separately:

- Arbitrary scheme X: `{X : Scheme.{u₁}}`. PASS. Neither the node nor Stacks
  derived.tex, section-ext (06XP), assumes a base field or finiteness. The source
  assumes an abelian category; X.Modules is the recorded category of O_X-modules.
- Ext of O_X-modules: `Ext F G i` is the source abbreviation for `Abelian.Ext`.
  Read def-sc-ext-sheaf and the source Ext.lean signature and definition: it is
  derived-category Ext, with the corrected resolution interpretation of the node.
  `[HasExt.{u₁} X.Modules]` is the recorded universe infrastructure available for
  this Grothendieck category, not an additional geometric restriction. PASS.
- Four modules F, F', G, G': `(F F' G G' : X.Modules)`. PASS: all are arbitrary;
  finite local freeness is imposed only on the first argument of the dependency
  comparison, never on these four modules in the item.
- Degree i >= 0 and class e: `(i : ℕ) (e : Ext F G i)`. PASS, including i=0.
- Morphisms u:F' -> F and phi:G -> G': `(u : F' ⟶ F) (φ : G ⟶ G')`.
  PASS: directions and shared scheme agree with the node.
- Contravariance: `(((Abelian.extFunctor i).map u.op).app G) e` equals
  `(Abelian.Ext.mk₀ u).comp e (zero_add i)`. PASS. Read Basic.lean's extFunctor:
  its component is precomposition by mk₀ u. Ext.comp is in diagrammatic order,
  so this is precisely e composed with u, with the correct degree 0+i.
- Covariance: `((Abelian.extFunctorObj F i).map φ) e` equals
  `e.comp (Abelian.Ext.mk₀ φ) (add_zero i)`. PASS. Read extFunctorObj and Ext.comp:
  this is postcomposition by phi shifted to degree i, with degree i+0.
- Canonical Ext(O_X,G)=H^i(X,G) and naturality: the third conjunct quantifies
  `a : Ext (SheafOfModules.unit X.ringCatSheaf) G i` and equates transport of
  the Ext image with `(RingedSpace.moduleCohomology X.toRingedSpace i).map φ`
  of the transported class. PASS. Read def-sc-sheaf-cohomology-functor and its
  RingedSpaceModuleCohomology declaration: H here is right-derived global
  sections in module sheaves. The existing G.H comparison instead targets
  cohomology of underlying abelian sheaves and does not state this square.
- In particular, H^i(phi)(x)=phi[i] composed with x: the fourth conjunct quantifies
  every `x : (moduleCohomology X.toRingedSpace i).obj G`, uses the inverse
  unitExtModuleAddEquiv to interpret x in Ext, composes with mk₀ phi, and
  transports forward. PASS. This is the stated formula under the comparison,
  without assuming an equality of the two carriers. It follows from the preceding
  clauses but is expressly present in the node; no extra conclusion is introduced.

Dependency module H13 reading:

Read lem-sc-ext-locally-free's full statement and five proof steps, and the
recorded LocallyFreeExtCohomology declarations. The delivered replacement covers
all F with `[F.IsFiniteLocallyFree]`, all G and i, with target cohomology of
`(tensorLeft Fᵛ).obj G`, and specializes to the tensor unit. Read Dual.lean:
Fᵛ is internal Hom(F,O_X), and dualEvaluation supplies the unit specialization.
Read HomTensor.lean: dualTensorHom is the recorded evaluation morphism;
locallyFreeHomSection applies its inverse to the global Hom section, using the
existing isIso_dualTensorHom_of_isFiniteLocallyFree theorem. No private evaluation
or tensor/Hom definition is introduced. Also read the tensor, internal-Hom and
module-category dependency node records: their operations specialize to these
same X.Modules objects.

The new equivalence is not an arbitrary uncharacterized Nonempty choice.
exists_locallyFreeExtModuleComparison specifies its value for every injective
resolution I, every resolution J of F-dual tensor G, and every augmentation-
compatible chain-map lift k. The differential compatibility condition covers
all n -> n+1; other differentials are zero for ComplexShape.up ℕ. Its final
quantifiers cover every cocycle f, identify the section in J's cycles, then
identify its homology class transported by moduleResolutionCohomologyIso.
Read Mathlib InjectiveResolution.extMk_surjective: every Ext class is represented
by such f. Finite-local-free tensor is exact and preserves injectives, so lifts
exist; hence this condition determines the canonical comparison on every class.
moduleResolutionCohomologyIso is the actual Mathlib isoRightDerivedObj, not an
arbitrary chosen isomorphism. locallyFreeExtModuleAddEquiv chooses an equivalence
from this named existence theorem; unitExtModuleAddEquiv uses dual evaluation and
left unitor. All definition data are explicit terms or chosen from a named theorem.
Only the two named theorems have sorry proofs; nothing is proved in this delivery.
The replacement dependency node changes only lean, with its required explanatory
note. There are no new nodes or statement_change records to review.

Sources: local literature/stacks-project and the dependency's blueprint source
are absent on this machine. Read official Stacks pages and fetched the official
Stacks repository derived.tex, cohomology.tex, and tags/tags into this item's
scratchpad. Read section-ext and lemma-compute-ext-resolutions (06XP/06XR),
section-cohomology-sheaves (01DZ), including its module-sheaf paragraph,
lemma-h1-extensions (0B3A), and lemma-injective-tensor-finite-locally-free (01E7).
These require only an abelian category or ringed space, and finite local freeness
for the dependency tensor comparison. No extra scheme hypotheses are hidden.
The blueprint file remains unavailable, so the dependency review follows its
full DAG statement and proof together with these primary Stacks sources.

Edge cases: i=0 gives ordinary Hom composition and Hom(O_X,G)=Gamma(G).
The formulas allow identity or zero u/phi and zero Ext/cohomology classes.
Zero modules and the empty scheme are not excluded by any binder. The dependency
allows F=0 and varying finite ranks on disconnected schemes; F=O_X is finite
locally free even on the empty scheme. There is no index set in the item; empty
cover/rank-zero behavior is allowed by the finite-locally-free predicate. There
is no characteristic, base field, properness, separatedness or Noetherian
restriction. Scheme.{u₁} is arbitrary in its universe, and all of its modules
use the recorded X.Modules universe; no independent too-small test universe is
introduced. All variables and universes are explicitly bound. No file-local
notation, private definition or local instance occurs in the statements.

Independent searches, logged in searches.jsonl:

- LeanFinder: "Canonical identification Ext from structure sheaf with derived
  global sections commutes with coefficient maps" returned global-section and
  degree-zero unitHomEquiv_comp_apply results, not this full statement.
- Loogle: "CategoryTheory.Abelian.extFunctorObj" returned extFunctorObj_map and
  extFunctor_map_app. Opened their definitions in Ext/Basic.lean. They give the
  two composition formulas, but do not give the scheme-module comparison square.
- LeanSearch: "Ext of a locally free sheaf is cohomology of its dual tensor
  naturally in coefficients" was unavailable (Internal Server Error); no verdict
  inferred from that service failure.
- Grep: "moduleCohomology|isoRightDerivedObj|unitHomEquiv_comp_apply" located
  Mathlib's resolution isomorphism and its naturality. Direct rg of Mathlib Ext,
  source WeilConjectures and project lean/Sheaf for Ext/cohomology naturality,
  unitExtModule and moduleResolutionCohomologyIso found only the already-read
  G.H comparison and its naturality, no full statement using moduleCohomology.
  Therefore existing:true would not render the whole node.

Mismatches and repairs: no mathematical or signature mismatch was found.
The dependency's module/theorem source citations incorrectly named 01E3, which
is the local killing of cohomology classes, not the tensor-injective fact.
Changed those citations to 06XR, 01DZ and 01E7. Removed the main module's unused
ExtYonedaAssociativity import: the Ext operation comes from the reused source
Ext definition via the comparison import; the associativity node remains cited
in the proof docstring. Signatures and all node statements remain unchanged.
Both node lean.statement strings were checked verbatim against their files.

Validation: final scompile of both modules together, dependency first, succeeded
in 5.6 seconds with exit code 0 and no errors or warnings. Every declaration has
its source and blueprint tag; theorem docstrings give the node proof steps.
