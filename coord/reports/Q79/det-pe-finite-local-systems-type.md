## Worker report

The module lean/Sheaf/AlgebraicGeometry/ProEtaleFiniteLocalSystemsType.lean states
AlgebraicGeometry.Scheme.finiteLocalSystemsType, with its proof entirely `sorry`.
It states the current blueprint's decomposition of a finite-presentation local
system by the isomorphism type of its module models. No definition is introduced,
no theorem is proved, and no mathematical statement is corrected.

Hypotheses and conclusions, clause by clause:

- The arbitrary scheme is `(X : Scheme.{t})`. The discrete commutative ring is
  `(Λ : Type u) [CommRing Λ]`; no topological structure is imposed. The independent
  universe parameters t and u are preserved.
- The small pro-etale site is `ProEt.topology X`, on `X.ProEt`. The coefficient
  ring sheaf is the `constantSheaf` in CommRingCat of `ULift.{t + 1, u} Λ`,
  followed by `sheafCompose` forgetting commutativity. This is exactly the ring
  used by the recorded local-constancy declaration, with coefficient and module
  universe `max u (t + 1)`. The lift is a size encoding of Λ, not a new ring.
- `F : SheafOfModules` of that coefficient sheaf is the specified Λ_X-module
  sheaf. `hF` uses
  `IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses X Λ` with predicate
  `Module.FinitePresentation (ULift Λ)`. Expanding this recorded definition gives
  a pro-etale covering of X, varying finitely presented module models, and
  isomorphisms of localized module sheaves. Thus local constancy and finite
  presentation are asserted on the same trivializing cover. Neither ordinary
  pointwise finiteness nor global constancy is substituted.
- `(R : Type v)` and `model : R → ModuleCat ...` encode the set of representatives.
  `hmodel` says every representative is finitely presented. `hrep` says each
  finitely presented module is isomorphic to exactly one `model r`. Together
  these say exactly one representative per isomorphism class, with no repetitions.
  Arbitrary v is allowed; there is no Small, Finite, Nonempty, or decidable-equality
  assumption on R.
- `∃ U : R → X.Opens` gives the pieces, with open subscheme structure
  `(U r).toScheme` and canonical open immersion `(U r).ι`.
  `IsClopenDecomposition X R U` is the already recorded predicate giving pairwise
  disjoint opens with supremum ⊤. Each is closed because its complement is the
  union of the other opens. This reuses the existing predicate, not a copy.
- `Nonempty (IsColimit (Cofan.mk X (fun r ↦ (U r).ι)))` says precisely that these
  inclusions exhibit X as their coproduct in Scheme, including its universal
  property. It avoids a Small hypothesis solely to access a chosen coproduct.
- For each r the conclusion gives a family `V : I → X.ProEt` and arrows
  `V i ⟶ ProEt.mk (U r).ι` that belongs to `ProEt.precoverage X`. This is a
  pro-etale trivializing cover of that open subscheme. Equivalently, it is the
  corresponding family in the localized site over that object. A morphism
  between weakly etale X-objects is weakly etale, and the covering condition is
  the fpqc condition on the actual schemes and arrows, independent of which
  base is used. Thus no canonical site comparison functor needs to be chosen.
- On each member `Nonempty (F.over (V i) ≅
  proEtaleConstantModuleSheafOverOfUniverses X Λ (V i) (model r))` gives the
  required isomorphism as module sheaves with the fixed model indexed by r.
  By the recorded `overFunctorMap` restriction compatibility, restricting first
  to the piece and then to V is the same as `F.over (V i)`. The recorded constant
  construction sheafifies the constant model over the restricted coefficient
  ring. This is the specified local triviality of F restricted to the piece.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Sites.Proetale:
  AlgebraicGeometry.Scheme.ProEt, ProEt.mk, ProEt.topology, ProEt.precoverage.
- Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses:
  AlgebraicGeometry.Scheme.IsLocallyConstantProEtaleModuleSheafWithModelsOfUniverses,
  proEtaleConstantModuleSheafOverOfUniverses; the primary recorded predicate
  IsLocallyConstantProEtaleModuleSheafOfUniverses is its specialization to all models.
- Mathlib.AlgebraicGeometry.OpenImmersion: AlgebraicGeometry.IsOpenImmersion;
  Mathlib's Scheme.Opens supplies the open subschemes and inclusions.
- Mathlib.CategoryTheory.Sites.ConstantSheaf: CategoryTheory.constantSheaf.
- WeilConjectures.CategoryTheory.ModuleObjects.Free:
  CategoryTheory.Mod.IsFinitelyPresented, read in the side framework. The dependency
  has no lean record but has a closed slopmaster2 audit recording this declaration.
  Its definition is the cokernel of a map between finite sums of the regular module.
  No dependency repair or duplicate declaration is needed.
- Mathlib.Algebra.Module.FinitePresentation: Module.FinitePresentation is the
  ordinary-module specialization used for the coefficient models. The existing
  landed node def-sc-finitely-presented-module records this exact declaration;
  the item's stmt_deps gains that node. Its finite generators and finitely generated
  relation kernel are equivalent to the finite-free cokernel presentation in the
  statement. The general internal-module predicate is not misapplied to ModuleCat.
- Sheaf.AlgebraicGeometry.CoproductCopiesMorphismsClopen:
  AlgebraicGeometry.IsClopenDecomposition. This is already supplied by the item's
  existing proof dependency lem-galois-coproduct-copies-morphisms-clopen.
- Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous:
  SheafOfModules.overFunctor, over, overMap, overFunctorMap.

The stated proof-dependency modules are imported for stage 3: ProEtaleSiteComparison,
ProEtaleComparisonPullbackSections, EtaleSetInverseImageConstantSheaf,
ConstantSheafSetsRepresentable, CoproductCopiesMorphismsClopen,
ProEtaleFiniteConstantHom, SiteCoveringAxioms, and Mathlib's Sites.Fpqc and
AlgebraicGeometry.Limits. The constant-sheaf global-section adjunction dependency
and scheme-coproduct dependency have their declarations in already imported
Mathlib modules. The theorem docstring includes all eight steps of the DAG proof
and the cited node ids, including empty-overlap gluing and empty-piece triviality.

Edge cases checked before writing:

- Empty X: every U r can be empty; its empty trivializing family is fpqc,
  and the inclusions of empty pieces exhibit the empty scheme as coproduct.
- An empty individual piece is permitted. Its cover index I is not Nonempty,
  and no model is forced to have a point in that piece.
- Empty R: hrep cannot hold, because the zero module is finitely presented.
  No separate nonemptiness assumption is added; every genuine representative
  system already includes its isomorphism class.
- Zero modules, zero ring, and presentation ranks m or n equal to zero are
  admitted by Module.FinitePresentation. No faithful/nonzero/free condition is added.
- Infinitely many representatives and infinitely many nonempty pieces are allowed.
  Cofan and IsColimit state the coproduct universal property without an extra
  indexing-universe equality or smallness assumption.
- X need not be connected, quasi-compact, quasi-separated, or Noetherian.
  Models and Λ need not be finite as sets. Coverings retain the fpqc finite
  refinement condition; joint surjectivity alone is not substituted.

Searches for an existing statement (all run through msearch.py where applicable):

- LeanFinder, "A locally constant proetale sheaf of finitely presented modules
  decomposes a scheme into clopen subschemes by module isomorphism type": eight
  hits, on CondensedMod/LightCondMod explicit sheaves and CompHausLike locally
  constant module functors. None decomposes a scheme by model isomorphism type.
- Loogle, "Module.FinitePresentation, AlgebraicGeometry.Scheme": zero hits.
- Mathlib grep in AlgebraicGeometry,
  `isomorphismType|[Ll]ocally[Cc]onstant.*[Cc]lopen|[Cc]lopen.*[Ll]ocally[Cc]onstant`:
  zero hits.
- LeanSearch, "A locally constant sheaf of finitely presented modules on the
  proetale site decomposes its scheme into open and closed loci of fixed module
  isomorphism type": eight hits, principally SheafOfModules finite-presentation
  predicates and constant-sheaf constructors, plus condensed locally constant
  functors. None states the requested decomposition.
- rg of the same clopen/model patterns and the node id in the upstream source
  and lean/Sheaf found the stalk zero-locus clopen theorem, topology helpers, the
  existing IsClopenDecomposition predicate, and downstream proof citations of
  this item. None states this item. An additional name search found no existing
  `finiteLocalSystemsType`. The upstream index/DAG audit identifies the existing
  internal-module finite-presentation definition, so it is imported, not restated.

Validation: the prescribed scompile.py compiled both sandbox and library forms
successfully, with no errors or warnings (8.2 s and 4.5 s). Every variable and
universe is explicitly bound. The only postponed proof is the named theorem
AlgebraicGeometry.Scheme.finiteLocalSystemsType, matching this item's DAG node.
No statement dispute, dependency fault, or new node was found.

## Second reading by Q79

Independent maintainer reading, 2026-10-18, of immutable delivery
8b3b9becd3461b4c0d4067d19448a70c7c6f6e11. The reviewer did not author this delivery.
This section replaces the delivered placeholder; the Worker report is retained.

The item and all six statement-dependency nodes were read from the immutable
snapshot. The actual Lean module, its module and theorem docstrings, and the
recorded declarations were read, rather than inferred from their names.

Clause-by-clause reading:

- `X : Scheme.{t}` and `Λ : Type u` with `CommRing Λ` introduce exactly the
  arbitrary scheme and discrete commutative ring. There is no connectedness,
  Noetherian, qcqs, nonzero, finite-set, or field assumption. Verdict: matches.
- The coefficient object in `F : SheafOfModules` is `constantSheaf` on
  `ProEt.topology X`, followed by the forgetful functor from commutative rings.
  Mathlib's constantSheaf is constant-presheaf sheafification. `ProEt` consists
  of weakly etale X-schemes; its precoverage is the pullback of the genuine fpqc
  weakly-etale precoverage. Verdict: the specified small pro-etale module category.
- `hF` expands the recorded WithModelsOfUniverses predicate with
  `Module.FinitePresentation` as its model predicate. It provides one covering
  of the final object, finitely presented varying models, and actual isomorphisms
  on localized ringed sites. The constant-module definition sheafifies the
  constant module with its given scalar action; it contains real data. Verdict:
  precisely the finite-presentation local triviality in the node.
- `R`, `model`, `hmodel`, and `hrep` encode finitely presented representatives,
  existence of a representative for each finitely presented module, and uniqueness
  of its index up to module isomorphism. Applying uniqueness to a representative
  excludes duplicate isomorphism classes. Verdict: exactly the representative set.
- `U : R → X.Opens` supplies the open subscheme structures and canonical open
  immersions. The reused IsClopenDecomposition predicate is pairwise disjointness
  and supremum top. The complement of any piece is the union of the others,
  so every piece is also closed. Verdict: all topological clauses are present.
- `Nonempty (IsColimit (Cofan.mk X ...))` says the inclusions have the scheme
  coproduct universal property. It avoids an unnecessary Small assumption on R.
  Verdict: the displayed disjoint union is a scheme decomposition.
- For each r the conclusion supplies a precoverage family over `ProEt.mk (U r).ι`
  and actual isomorphisms `F.over (V i) ≅ ... (model r)`. The precoverage tests
  the underlying scheme arrows, so this is also the required covering of the
  open in its localized site. SheafOfModules.overFunctorMap identifies iterated
  restriction with restriction directly to V i. Verdict: precisely local
  constancy with that fixed model on the piece, including empty pieces.

Dependency and source checks:

- Read the blueprint item and proof at
  literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
  sk-prop-pe-finite-local-systems/sk-prop-pe-finite-local-systems-type{,.proof}.md.
  Its arbitrary discrete ring and finite-presentation models are retained.
- Read ProEt, ProEt.mk, precoverage, topology in Mathlib's Sites/Proetale.lean;
  constantSheaf in CategoryTheory/Sites/ConstantSheaf.lean; IsOpenImmersion in
  AlgebraicGeometry/OpenImmersion.lean; and over, overMap, overFunctorMap in
  Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean.
- Read the complete recorded module
  Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses, including its construction
  of constant modules, localized construction, and model-predicate variant.
  The local-bijectivity obligations are named theorems, not missing data.
- Read CategoryTheory.Mod.IsFinitelyPresented in the group clone's side-framework
  lean/WeilConjectures/CategoryTheory/ModuleObjects/Free.lean, including finiteFree.
  It is the audited internal-module finite-free cokernel predicate. The delivery
  correctly uses Module.FinitePresentation for ordinary coefficient modules,
  via the already-landed def-sc-finitely-presented-module, rather than applying
  that internal-module predicate to an unrelated category. The landed dependency
  addition is permitted by stage2_delivery.py's STMT_DEPS MAY GAIN LANDED NODES rule.
- Read Stacks sites.tex, example-constant-sheaf (0H7J), schemes.tex definitions
  01HE/01IO, and algebra.tex definition-module-finite-type (0518). Read
  Bhatt--Scholze 4.1.1, 4.1.2, 4.2.10, 4.2.12 and 7.3.1(1). The latter section's
  locally topologically noetherian convention is not an added hypothesis of the
  blueprint's general module definition: coverwise constancy makes sense for all X,
  and the item proof uses no noetherian consequence.
- Read IsClopenDecomposition in CoproductCopiesMorphismsClopen.lean and the exact
  finiteConstantHom_constant statement, including its coefficient normalization,
  composition and identity clauses. The eight proof steps in the delivered
  theorem docstring track constant sections, local uniqueness, label gluing,
  clopen fibres and restriction of the actual trivializing cover. These are
  proof instructions; no proof of the item is supplied at this stage.

Sizes and edge cases: t,u,v are explicitly bound and autoImplicit is false.
There is no t=u constraint. The ring lift and module universe max u (t+1)
are those of the recorded local-constancy interface. Finitely presented models
have small finite-free presentations; the encoding does not exclude a module
isomorphism class. The arbitrary representative index universe v is retained.
The covering index has the recorded small-site size t+1. Empty X and empty
pieces admit empty covering families; no Nonempty I is required. Empty R cannot
satisfy hrep because the zero module is finitely presented. Zero rings and zero
modules, ranks zero, infinite representative sets, and non-quasicompact X remain
allowed. No cardinal bound is imposed solely to select a coproduct object.

One-definition-per-notion: the report records LeanSearch, LeanFinder, Loogle
and grep searches. Independent rg searches in upstream WeilConjectures,
the group clone's lean/Sheaf, and Mathlib/AlgebraicGeometry for model/type-locus
and locally-constant/clopen formulations found zero-locus and topological helpers,
not this decomposition theorem. The exact theorem name has no competing
existing declaration. The delivery reuses the recorded constant-module and
clopen-decomposition definitions and introduces no definitions of its own.

Maintainer gates: the node's lean.statement is byte-for-byte the module signature
up to `:= by`; the theorem body is only `sorry`. Both docstrings name the source
and blueprint, and the theorem docstring contains all eight node proof steps.
No Lean line exceeds 100 characters. Imports use the allowed namespaces; proof
imports are explicitly accounted for in the worker report and proof docstring.
There are no new nodes, dependency modules, statement corrections, or citer
changes. No missing helper construction is needed to type this statement.
No pro-etale substitute, arbitrary map, or hollow construction is used.
The item has no route-pivot repair note at the inspected shared origin reference;
none of its statement/proof dependencies is on route-pivot-dropped.txt, and its
proof does not reintroduce enhanced/model-category machinery.

Compiler evidence: reran exactly
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q79 det-pe-finite-local-systems-type snapshot/lean/Sheaf/AlgebraicGeometry/ProEtaleFiniteLocalSystemsType.lean`.
Exit code 0; sandbox Sheaf/Stage2/Sandbox0.lean passed in 13.4 s, library
Sheaf/AlgebraicGeometry/ProEtaleFiniteLocalSystemsType.lean passed in 25.8 s,
with no diagnostics. The installed wrapper now delegates to the server's private
side overlay (reported /dev/shm/nt-tmp/nt-local-compile-j61ybd7n/.lbuild), rather
than compiling on this host. Only the prescribed wrapper was invoked; no direct
SSH, lake build, global build, or live Lean edit was performed.

Finding H11 (and the real-section requirement of H1): the delivered Second
reading section was only an explicit disclaimer of a reading. Replaced it with
this independent substantive reading in a complete report replacement. No Lean,
node, statement, or mathematical correction is needed. The immutable snapshot
was not edited and no branch head was changed.
