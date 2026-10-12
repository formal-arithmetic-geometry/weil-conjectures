## Worker report

The delivery contains two modules. `Sheaf.AlgebraicGeometry.AlternatingCechTotalComplex`
constructs the general finite-family alternating Čech functor with explicit data;
`Sheaf.AlgebraicGeometry.QCohComplexAlternatingCechDerivedSections` states its derived
comparison for termwise quasi-coherent complexes. Every new theorem has proof `sorry`.
No construction selects data from a sorried existence theorem. No statement is disputed.

Hypothesis and clause correspondence for the corrected item:

| Node text | Lean rendering |
| --- | --- |
| Arbitrary scheme X | `(X : Scheme.{u})` |
| Finite family, including r=0 | `(r : ℕ) (U : Fin r → X.Opens)` |
| The family covers X | `(hU : iSup U = ⊤)` |
| All intersections indexed by a nonempty tuple are affine | `hAffine : ∀ (p : ℕ) (t : Fin (p + 1) → Fin r), IsAffineOpen (⨅ k, U (t k))`; repetitions are permitted, and this does not exclude empty open intersections |
| Complex of O_X-modules, with no boundedness | `F : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ` |
| Every term is quasi-coherent | `hF : ∀ n : ℤ, (F.X n).IsQuasicoherent` |
| Derived categories of O_X-modules and global-ring modules | The two `HasDerivedCategory.{w}` / `HasDerivedCategory.{v}` binders, respectively on the shared sheaf carrier and `ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))` |
| The actual alternating total, rather than an arbitrary complex | `(alternatingCechTotalFunctor U).obj F` |
| Existence of the canonical comparison (i) | First conjunct: `∃ β, IsAlternatingCechDerivedComparison U F β` |
| Every canonical comparison is an isomorphism (ii) | Second conjunct: `∀ β, IsAlternatingCechDerivedComparison U F β → IsIso β` |
| Functoriality on complexes of quasi-coherent modules (iii) | Third conjunct quantifies `G`, `_hG`, `g : F ⟶ G`, `βF`, `βG` and both comparison predicates, then states `Q.map (Tot.map g) ≫ βG = βF ≫ RΓ.map (Q.map g)` |

Definition-node correspondence:

- `alternatingCechIntersection U t` is `⨅ k, U (t k)`, indexed by
  `t : Fin (p + 1) ↪o Fin r`. `alternatingCechTerms` is the genuine dependent product
  module `ModuleCat.of _ (∀ t, G.obj (op (alternatingCechIntersection U t)))`.
- `alternatingCechDifferential` is the finite sum over `j : Fin (p + 2)` with sign
  `(-1 : ℤ)^j.val`. The face is `(Fin.succAboveOrderEmb j).trans t`, so it is exactly
  `t ∘ succAbove j`. Its restriction uses the inclusion of the full intersection
  into the face intersection. `LinearMap.proj`, `LinearMap.comp`, finite sums of
  linear maps, and `LinearMap.pi` provide all linear-map data directly.
- `alternatingCechComplex` is `CochainComplex.of` of those terms and differential;
  only the square-zero identity is postponed. `alternatingCechTermsMap` applies
  the presheaf map at the intersection to each factor. `alternatingCechComplexMap`
  and `alternatingCechComplexFunctor` use named commutation and functor-law proofs.
- `alternatingCechModulePresheaf` is exactly `SheafOfModules.forget _ ⋙
  PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op`, on the shared
  `moduleRings` carrier, without creating another scalar-action convention.
- `alternatingCechModuleFunctor` composes this with the alternating complex functor
  and `ComplexShape.embeddingUpNat.extendFunctor`. This is zero extension to ℤ.
  The named additive proof is used as an instance, not as unspecified data.
- `alternatingCechDoubleFunctor` applies that functor termwise to F, then uses
  `HomologicalComplex₂.flipFunctor`. Consequently the first index is the Čech
  degree, the second is the coefficient degree. `alternatingCechTotalFunctor`
  composes with `HomologicalComplex₂.totalFunctor`. Its object and map are
  Mathlib's `HomologicalComplex₂.total` and `HomologicalComplex₂.total.map`.
  Mathlib's integer total convention is d₁ + (-1)^p d₂ with this ordering.
- `alternatingCechPresheafZero` is the product of restrictions from the top open
  to the intersections in degree zero. `alternatingCechZero` first uses the
  existing identity-restriction scalar isomorphism from ModuleCechComparison,
  then these restrictions, then `extendXIso.inv` to enter integer degree zero.
- `alternatingCechAugmentationComponent` includes that zero Čech row with
  `ιTotal (ComplexShape.up ℤ) 0 n n (Int.zero_add n)`. It has no positive-row
  components. The commutation and naturality identities are named theorems,
  used to construct the chain map and natural transformation explicitly.
- `IsAlternatingCechDerivedComparison U F β` quantifies every K-injective J and
  every quasi-isomorphism i:F→J, and states exactly
  `β ≫ RΓ.map (Q.map i) ≫ (rightDerivedFunctorObjQIso J).hom ≫
  Q.map (augmentation.app J) = Q.map (Tot.map i)`. The predicate defines no chosen
  comparison and assumes neither an arbitrary total nor arbitrary augmentation.

Dependencies read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.Coherent`: the node's recorded `RingedSpace.IsCoherent`
  is not the quasi-coherence clause; its docstring explicitly identifies that
  clause with Mathlib `SheafOfModules.IsQuasicoherent`, which is what hF uses.
- `Sheaf.CategoryTheory.SiteCechComplex`: `CategoryTheory.SiteCechComplex` is the
  full-site, all-tuples Čech construction, not this increasing-tuples functor.
  The correction replaces this statement dependency with the new definition.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory` uses the same
  `HasDerivedCategory` binder on `SheafOfModules (moduleRings X.toRingedSpace)`.
- `Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage`: `schemeDerivedDirectImage`
  is the recorded scheme-to-scheme functor. Global sections has a module-valued
  codomain, so the corrected statement names its existing `globalSectionsFunctor`
  instead; no new definition of global or derived sections is introduced.
- `Sheaf.AlgebraicGeometry.ModuleCechComparison`: reuse
  `Scheme.Modules.moduleCech_top_restriction` and its prescribed forgetful
  composite. Read `moduleCechDouble`, `moduleCechAlpha`, `IsModuleCechComparison`
  in full as the model. The latter predicate is for single-module cohomology.
- `Sheaf.Topology.RingedSpaceModuleCohomology`: reuse
  `RingedSpace.globalSectionsFunctor` and its additive instance.
- `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage`: reuse the shared
  `RingedSpace.moduleGrothendieckAbelian` instance; K-injective resolutions are
  inferred from this existing structure without adding a hypothesis on X.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`.
  `Mathlib.Algebra.Category.ModuleCat.Sheaf`: `SheafOfModules`.
  `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`: `CochainComplex.IsKInjective`.
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`:
  `CategoryTheory.Functor.rightDerivedFunctorObjQIso` with its full signature.
  Its orientation is RΓ(QJ) → QΓ(J), the orientation used in the equation.
- Mathlib's `HomologicalComplex.extendXIso`, `ComplexShape.embeddingUpNat`,
  `HomologicalComplex₂.flipFunctor`, `totalFunctor`, `total.map`, and `ιTotal`
  supply the extension, index exchange and totalization API.

The main theorem imports every already-stated proof dependency, including the
finite-filtration spectral comparison, injective Čech acyclicity, affine derived
equivalence and K-injective restriction modules. The last two K-injective
comparison dependencies are Mathlib leaves, available through the imported
K-injective derived-functor module. The docstring carries all five proof steps
of the item, with their node citations.

Edge cases checked before writing:

- r=0: Fin 0 admits no increasing tuple of length p+1. Every nonnegative Čech
  term is the empty product module, hence zero. Negative terms are zero by
  extension, and the total is zero. The cover equality forces the scheme to
  be empty; sections and derived sections are zero. No nonempty-index or
  positive-r binder excludes this case.
- F=0: every section factor and differential is zero, hence so are the
  alternating total and derived sections. The canonical equation specializes
  to the zero-object equation.
- Unbounded F: the coefficient index is ℤ without a boundedness predicate.
  Increasing tuples are absent for p≥r, so only the finitely many Čech rows
  0,…,r-1 contribute to each total degree. Although Mathlib uses its general
  coproduct totalization, this finite support gives the source's finite total.
- Empty opens and repeated indices: hAffine quantifies all nonempty tuples,
  including repetitions and tuples with empty intersection; the cochains
  themselves use increasing tuples only. Empty affine intersections are allowed.
- All variables/universes are explicit. The w,v derived-category binders are
  the standard chosen-localization size parameters; u is shared by the scheme,
  sheaf modules, global coefficient ring and section modules.

Searches made with the launcher's msearch.py (all recorded in searches.jsonl):

- LeanFinder: `alternating Cech complex of a finite open cover computes derived
  global sections of an unbounded quasicoherent complex`: eight hits on sheaf
  cohomology and Mayer–Vietoris, no matching comparison.
- Loogle: `HomologicalComplex₂.total, HomologicalComplex.extend`: zero hits.
- Grep Mathlib CategoryTheory: `alternatingCech|AlternatingCech|cechComplexFunctor`:
  only the two mentions of the full `cechComplexFunctor` in SheafCohomology/Cech.
- LeanSearch: `alternating Cech total complex of a finite open cover with canonical
  comparison to derived global sections`: unavailable, Internal Server Error.
- LeanFinder: `alternating Cech complex functor indexed by strictly increasing
  tuples for a finite open cover with augmentation and totalization of unbounded
  complexes`: eight hits on pairwise-cover functors, Dold–Kan and singular
  chains, none on this construction.
- Grep all Mathlib: `alternatingCech|AlternatingCech|alternating.*[Cc]ech`: zero hits.
- rg of WeilConjectures and lean/Sheaf for the same concept and the item id:
  the source contains usual Čech and monomial complexes; the project contains
  `alternatingCechComputes` and principal-open totals, but no general total functor.
  Exact proposed-name searches find no existing declaration.
- DAG name/concept search and `tools/blueprint_refs.py search alternating`: the
  proposed definition id is free; the nearby nodes are existential alternating
  comparisons or principal-open specializations. `ancestor` returns
  `lem-sc-finite-duality`.

## New nodes

`def-sc-alternating-cech-total-complex` defines the increasing-tuples cochain
functor, its zero extension, the Čech-first double and total functors, the
restriction augmentation, and the K-injective canonical-comparison predicate.
Its source is the supplied Stacks Cohomology excerpt, especially
`equation-global-sections-to-alternating-cech` and
`lemma-alternating-cech-complex-complex`. Its own TeX introduces every object,
ring, differential, map and resolution equation, and cites the existing notion
nodes. Its searches above establish that it is missing, rather than another
spelling of an existing definition. In particular
`def-sc-principal-open-alternating-total` is a specialization on Spec A with
principal opens and coefficient ring A; it cannot supply the general-scheme
construction. Its `Classical.choose` constructions were not copied. All 27
public declarations belong to the new node, including the named proof
obligations documented with their complete elementary arguments.

## Statement corrected

The original node informally introduced the increasing-tuples total and a
canonical comparison, but its dependency records gave neither the general
alternating total functor nor the canonical comparison equation. An arbitrary
Tot or an arbitrary map would lose the source's construction. The correction
supplies the missing definition and makes existence, invertibility of every
canonical comparison, and the functoriality square explicit. It changes no
geometric or boundedness hypothesis and does not change any unit statement.
The source is Stacks `lemma-alternating-cech-complex-complex` and Lemma 08C2,
with affine quasi-coherent vanishing, as used by Perfect Lemma 08D2. The source
excerpt was read before construction.

The full-site Čech and scheme-to-scheme derived-direct-image statement
citations are replaced by the new alternating definition and the existing
module-valued global-sections definition. The proof and proof_deps remain
verbatim unchanged. `statement_change` records old_statement verbatim and
old_stmt_deps, and contains every citer found by the DAG search.

The only citer is `lem-sc-affine-koszul-cech-derived-comparison`: **holds**.
Its second proof step applies this lemma to the restricted complex on the union
of principal opens. Those intersections are affine and all restricted terms
are quasi-coherent. The explicit general-scheme comparison is the same
functorial map used there, then restricted along A→Γ(U,O_U). That citer was
read in full and was not edited.

Local verification: both modules compiled with lcompile.py, including writing
.olean files, in about 5 and 4 seconds respectively, with no errors or warnings.
The final `deliver2.py Z2 lem-sc-qcoh-complex-alternating-cech-derived-sections
--no-push` failed before preflight because its multi-module compiler does not
support the project's module-system headers. Nothing was pushed.

Tool failure: `scompile.combine` uses `^import\s+(\S+)\s*$` to extract imports
and removes only lines beginning `import`. It therefore leaves both `module`
and `public import` commands inside each concatenated body. It also fails to
recognize the sibling public import. The remote combined file produced:

```
:18:0: error: unexpected identifier; expected command
:20:6: error: unexpected token 'import'; expected 'lemma'
:20:7: error: invalid 'import' command, it must be used in the beginning of the file
```

The error is in the wrapper's concatenation, before any declaration, not in the
modules (both compile cleanly with the module-aware local lcompile.py).
AGENTS.md §3 and §6 forbid workers from changing or working around a tool that
refuses correct work. The launcher must repair this wrapper to understand
`module`, `public import`, `@[expose] public section`, sibling dependency order,
and independently scoped universe declarations, or use a module-aware server
compilation routine. The worker has not altered any tool or weakened the files
to satisfy an obsolete concatenator. The sandbox is ready for rerunning the
dry run after that tool repair, then for the independent second reader.

Standalone server verification: scompile.py compiled AlternatingCechTotalComplex.lean
cleanly in 4.6 seconds. The failure is specific to combining module-system files.

Original statement for the correction record:

Let $U$ be a scheme [def-pc-scheme] with a finite open covering $\mathcal U:U=\bigcup_{i=1}^rU_i$ such that $U_{i_0\ldots i_p}=U_{i_0}\cap\cdots\cap U_{i_p}$ is affine for all $p\ge0$ and all $i_0,\ldots,i_p$. Let $\mathcal F^\bullet$ be a cochain complex of quasi-coherent $\mathcal O_U$-modules [pqf-def-coherent], not assumed bounded in either direction. Let $\operatorname{Tot}(\check{\mathcal C}^\bullet_{\mathrm{alt}}(\mathcal U,\mathcal F^\bullet))$ be the total complex of the double complex with terms $\check{\mathcal C}^p_{\mathrm{alt}}(\mathcal U,\mathcal F^q)=\prod_{i_0<\cdots<i_p}\mathcal F^q(U_{i_0\ldots i_p})$, the alternating Cech differential $d_1$ [def-weil-pbc-site-cech-complex] in the $p$-direction, the differential $d_2$ induced by $\mathcal F^\bullet$ in the $q$-direction, and total differential $d_1+(-1)^pd_2$ on the $(p,q)$ term. Then there is a canonical isomorphism $\operatorname{Tot}(\check{\mathcal C}^\bullet_{\mathrm{alt}}(\mathcal U,\mathcal F^\bullet))\to R\Gamma(U,\mathcal F^\bullet)$ in $D(\Gamma(U,\mathcal O_U))$ [def-pc-derived-category] [def-pc-derived-direct-image], functorial in $\mathcal F^\bullet$.

## Second reading by Z2

I read the corrected item and the new definition against stacks-altcech.tex first:
Cohomology's section on unbounded complexes, the global-section augmentation,
lemma-alternating-cech-complex-complex, Lemma 08C2, and Perfect Lemma 08D2.
08C2 requires vanishing for terms, cokernels and cohomology on a basis. On a
scheme the affine opens are a basis; all three sheaves are quasi-coherent,
so affine vanishing supplies these assumptions. No separated, Noetherian,
field, characteristic, or boundedness hypothesis is implicit in this application.
The source first uses K-injectives with injective terms. Its canonical roof
also characterizes the map through arbitrary K-injectives: compare with an
injective-term resolution by a homotopy equivalence and use naturality.

The objects, hypotheses and conclusion clauses, matched individually:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| An arbitrary scheme X | `(X : Scheme.{u})` | Exact; Mathlib Scheme is locally affine, without extra finiteness. |
| A finite family of opens, r possibly zero | `(r : ℕ) (U : Fin r → X.Opens)` | Exact; every finite indexed family can be enumerated this way. |
| The family covers X | `(hU : iSup U = ⊤)` | Exact and substantive. |
| Every nonempty-tuple intersection is affine | `hAffine : ∀ (p : ℕ) (t : Fin (p + 1) → Fin r), IsAffineOpen (⨅ k, U (t k))` | Exact: all lengths ≥1, all tuples, repetitions and empty intersections included. |
| Unbounded complex of O_X-modules | `F : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ` | Exact shared module carrier; both directions unbounded. |
| Every term quasi-coherent | `hF : ∀ n : ℤ, (F.X n).IsQuasicoherent` | Exact; not coherence or finite presentation. |
| Derived categories and coefficient ring | The two `HasDerivedCategory.{w}` and `.{v}` binders, with `ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))` | Chosen localizations in the standard size convention, with coefficient ring Γ(X,O_X). |
| The prescribed alternating total | `(alternatingCechTotalFunctor U).obj F` | The actual increasing-tuple construction, not a supplied unrelated complex. |
| Unbounded RΓ | `(RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor` | Existing module-valued Γ, derived using K-injectives. |
| (i) Canonical comparison exists | `∃ β, IsAlternatingCechDerivedComparison U F β` | Exact source roof, explicitly characterized. |
| (ii) Every such comparison is invertible | `∀ β, IsAlternatingCechDerivedComparison U F β → IsIso β` | Exact: the roof equation determines the canonical map because its resolution and augmentation factors are invertible. |
| (iii) Functoriality | `∀ G (_hG : ∀ n, (G.X n).IsQuasicoherent) (g : F ⟶ G) βF βG`, both predicates, then `Q.map (Tot.map g) ≫ βG = βF ≫ RΓ.map (Q.map g)` | Exact naturality square and quantifier order. No boundedness on G. |

I opened the dependency nodes and their recorded modules/signatures. Scheme
and Scheme.Opens are Mathlib's. The quasi-coherent clause of pqf-def-coherent
is Mathlib SheafOfModules.IsQuasicoherent, as Coherent.lean explicitly says;
RingedSpace.IsCoherent itself would be the wrong clause and is not used.
DerivedCategory.lean uses the same SheafOfModules carrier and localization
binder as this statement. RingedSpaceModuleCohomology.globalSectionsFunctor
is evaluation at the top open in modules over its section ring, not abelian
sheaf Ext. ModuleCechComparison.moduleCech_top_restriction supplies only the
identity-scalar comparison reused by the augmentation. Its all-tuples complex
and IsModuleCechComparison are not mistaken for the alternating construction.
RingedSpaceDerivedDirectImage.moduleGrothendieckAbelian supplies the existing
K-injective-resolution structure. Mathlib CochainComplex, DerivedCategory.Q,
QuasiIso and CochainComplex.IsKInjective match the respective notion nodes.
I read rightDerivedFunctorObjQIso: its orientation is RΓ(QJ) → QΓ(J), exactly
the orientation in the new predicate. No unusable dependency needs a new module.

The new definition node, clause by clause:

- `alternatingCechIntersection U t` is the infimum over the increasing tuple.
  `alternatingCechTerms` is the dependent product of the section modules over
  `Fin (p+1) ↪o Fin r`; these are exactly strictly increasing tuples.
- `alternatingCechDifferential` uses LinearMap.pi and the finite signed sum
  `(-1 : ℤ)^j.val`, deleting j by `Fin.succAboveOrderEmb j` and restricting
  along `alternatingCechIntersection_face_le`. This is the source face formula.
- The complex and its functor maps use explicit objects and linear maps;
  square-zero, commutation, functor laws and additivity are named proof
  obligations with source and natural-language proofs. None chooses data
  from an unproved existence statement, and no definition body has sorry.
- `alternatingCechModulePresheaf` restricts scalars from each open's ring along
  the top-open restriction, using the existing forgetful functor. Integer
  extension uses ComplexShape.embeddingUpNat, zero outside the nonnegative
  degrees. Coefficient complexes are indexed by all of ℤ.
- `alternatingCechDoubleFunctor` maps coefficient complexes then flips:
  the outer/first index is Čech degree p, the inner/second index is q.
  I checked ComplexShapeSigns.lean: TotalComplexShape has π(p,q)=p+q,
  ε₁=1 and ε₂=(up ℤ).ε p=p.negOnePow. TotalComplex.lean uses these factors
  in d₁ and d₂. Thus the total really has d_Cech + (-1)^p d_F.
- `alternatingCechZero` corrects the identity scalar restriction then maps
  sections to singleton intersections. `alternatingCechAugmentationComponent`
  includes this into total degree n using ιTotal at (0,n). No component in a
  positive Čech row is present. The chain map and natural transformation have
  explicit components, with only named identity proofs postponed.
- `IsAlternatingCechDerivedComparison` quantifies J, `[J.IsKInjective]`,
  `i : F ⟶ J`, `[QuasiIso i]`, and states
  β ≫ RΓ(Qi) ≫ ε_J ≫ Q(α_J) = Q(Tot(i)). The source roof gives exactly
  this equation. No comparison is selected and no invertibility is assumed.

The new node has the required definition id in the item's chapter, kind
`definition`, status `split`, self-contained TeX, exactly the cited stmt_deps,
source document/place, empty proof/proof_deps, null proof_origin/mathlib_match,
three search kinds (the unavailable LeanSearch is recorded as such), created
worker/item/date/group, ancestor and via, both lean_audit states `none`, matching
chapter/unit and lean record. The item cites it. There are no additional
dependency modules in this packet. The node is a general-scheme construction;
the existing principal-open specialization does not define this functor.

Edge cases: for r=0 each increasing-tuple indexing type is empty, giving the
zero product module; all negative Čech degrees are zero by extension. The
cover equality then forces X empty, so Γ and RΓ are zero. For F=0 all terms,
maps and derived sections are zero. For r=1 there is only Čech degree zero
and the augmentation is restriction to the sole cover member. For p≥r there
are no increasing tuples, so finitely many Čech rows contribute even when F
is unbounded. Repeated cover members and empty intersections are allowed by
hAffine. Signs use integer scalar action and work in every characteristic,
including 2. The scheme, section modules and sheaf modules share universe u;
v and w are localization sizes, with no vacuous test-object quantifier.
All variables/universes are bound; no local notation or local instance is used.

Independent searches (msearch.py recorded them in searches.jsonl): LeanFinder
`finite ordered open covering increasing sequences alternating cochains
augmentation derived sections` returned generic hom-complex constructions,
CochainComplex.augment and AlternatingCofaceMapComplex.obj, no matching object
or comparison. Loogle `AlgebraicTopology.AlternatingCofaceMapComplex.obj`
returned the cosimplicial alternating-coface construction: that object's
terms are those of a supplied cosimplicial object, not increasing cover tuples.
LeanSearch `strictly increasing tuples finite open cover alternating Cech
total complex` returned Internal Server Error (unavailable, no negative
search verdict inferred). Independent rg searches for increasing tuples,
strictly increasing, alternating/Čech and proposed names covered Mathlib,
WeilConjectures, lean/Sheaf and dag/nodes. I opened the upstream
CategoryTheory/Sites/CechComplex.lean and Topology/Sheaves/Cech.lean: their
terms use all functions Fin(p+1) → I. I opened AlternatingCechComputes.lean:
it existentially characterizes a single presheaf's alternating complex, not
the module-valued functor, total or augmentation here. PrincipalOpenCechTotal
is specific to Spec A and its principal opens, with A coefficients. None is
an exact reusable declaration of this new general construction or the item.

The statement_change old_statement agrees verbatim with the repository's
original item; old_stmt_deps agrees too. No proof or proof_deps was changed.
The original statement is reproduced below to make the correction report
self-contained. The correction supplies the missing construction without
changing the source's geometric hypotheses or unbounded conclusion.
A search of stmt_deps/proof_deps finds only ONE citer, so a second citer does
not exist to open. I opened lem-sc-affine-koszul-cech-derived-comparison and
AffineKoszulCechDerivedComparison.lean, together with PrincipalOpenCechTotal
and KoszulCechComparisonConstruction. Its `holds: true` verdict is correct:
apply this lemma on the union U of the principal opens, whose intersections
are affine and whose restricted terms remain quasi-coherent. Increasing tuples
and sorted nonempty subsets identify the two finite totals, with the same
horizontal and vertical signs and augmentation. Restriction of scalars along
A → Γ(U,O_U) gives the comparison in D(A). The equality characterizing the
principal-open comparison is the same roof equation. This requires transport
between these models in stage 3, not literal equality of Lean carriers. The
citer is not edited.

Mismatches repaired: the definition module lacked the required main-definition
list; I added it. The proof documentation did not explicitly justify why the
predicate covers K-injectives without injective terms, although the source's
construction starts with injective terms; I added the homotopy-equivalence
transport argument to the predicate docstring and theorem step 5. Both
lean.statement records normalized whitespace instead of copying the actual
multiline signatures; I replaced them with verbatim signatures. No mathematical
statement or construction was changed, and no theorem was proved.

Final validation: both modules compiled together with lcompile.py, cleanly,
with all theorem proofs remaining sorry. The known deliver2.py multi-module
fault is not rerun, per the launcher's explicit instruction; delivery is left
to the launcher.
