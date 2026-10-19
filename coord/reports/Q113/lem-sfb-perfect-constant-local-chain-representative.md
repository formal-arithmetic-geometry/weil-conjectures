## Worker report

The delivery states `CategoryTheory.exists_perfect_constant_local_chain_representative`
in `Sheaf.CategoryTheory.PerfectConstantLocalChainRepresentative`, following Stacks
09BD (`lemma-map-out-of-locally-constant`) and its input 08FR(1). Its only theorem
has proof `sorry`; its docstring gives the node's six-step proof, including the
finite descending homotopy induction and both cone component equations. The
statement, proof, and proof dependencies of the DAG node are unchanged.

Clause-by-clause correspondence:

- Small site: `{C : Type u} [Category.{v} C]`, `J : Precoverage C`, and
  `_hJ : J.IsSiteForCoverings`, exactly the recorded site interface. Object and
  morphism universes are independent. Sheaves use `J.toGrothendieck`.
- Final object: `(X : C) (_hX : IsTerminal X)`.
- Commutative ring: `(R : Type (max u v)) [CommRing R]`. The coefficient universe
  contains the site data, as in the already landed parent theorem and constant
  module functor. This is a size convention, not a finiteness assumption on R.
- Cochain complex of R-modules: `F : CochainComplex (ModuleCat R) ℤ`.
- Boundedness in exactly the node's sense: `_hbounded` asserts existence of
  integers `a ≤ b` and `IsZero (F.X q)` whenever `q < a ∨ b < q`.
  This concerns terms, not just cohomology. A categorically zero module is
  exactly a zero module, without requiring literal equality to a chosen object.
- Finitely generated terms: `[∀ q : ℤ, Module.Finite R (F.X q)]`.
- Projective terms: `[∀ q : ℤ, Module.Projective R (F.X q)]`. Neither freeness
  nor projectivity as sheaf objects is assumed.
- Constant ring sheaf: `(constantSheaf J.toGrothendieck RingCat).obj
  (RingCat.of R)`. The constant module complex is
  `(constantModuleCochainFunctor J.toGrothendieck R).obj F`, the termwise
  application of the recorded `siteConstantModuleFunctorGeneral`, with its
  differentials sent by that same functor.
- Arbitrary target complex: `G : CochainComplex (SheafOfModules S) ℤ`, where S
  is that exact constant ring sheaf. No boundedness, perfectness, finite type,
  or injectivity hypothesis is imposed on G.
- Localization Q: `DerivedCategory.Q`. The `siteModuleHasDerivedCategory`
  binders choose the morphism universes of the localized categories, globally
  and on slices; they impose no geometric or homological condition. There is
  no derived-category hypothesis on the coefficient modules because this
  statement localizes only the sheaf complexes.
- Every derived morphism: the unrestricted binder
  `ψ : Q.obj (constant F) ⟶ Q.obj G`.
- Actual covering family: `∃ (I : Type (max u v)) (U : I → C)
  (f : ∀ i, U i ⟶ X), Presieve.ofArrows U f ∈ J X ∧ ...`.
  There is no nonempty-index restriction and no replacement by a merely
  Grothendieck-covering sieve.
- Local chain maps: `∀ i, ∃ a : (moduleCochainRestriction S (U i)).obj
  (constant F) ⟶ (moduleCochainRestriction S (U i)).obj G`.
  These are morphisms of the cochain-complex category, hence genuine chain maps.
- The equation `Q(a) = ψ|U_i`: `DerivedCategory.Q.map a` equals the image of ψ
  under `ringedDerivedRestrictionSized S (U i)`, conjugated by the inverse
  source and forward target components of `moduleCochainRestrictionQIso`.
  Those components are precisely Mathlib's canonical
  `Functor.mapDerivedCategoryFactors.app`, not chosen or assumed comparisons.
  This conjugation is necessary because localization commutes with restriction
  canonically rather than by literal equality of its object expressions.
- Localized ringed sites: `SheafOfModules.overFunctor S U` takes values in
  modules over `S.over U` on `J.over U`; the restriction of complexes applies it
  degreewise. It is exactly the restriction recorded by
  `def-pur-localized-ringed-site`.

The three helper definitions only package canonical existing functors and the
localization comparison with their required instances. Each has real data and
a source/blueprint docstring; none chooses an object using a postponed existence
claim. They are listed in `lean.declarations`. No theorem has been added for an
unrecorded auxiliary claim. The zero-map, finite-limit and finite-colimit
instances are supplied inside definition bodies from the existing exactness
theorems. There are no file-local instances or notation and no hidden `let`
binders in the theorem signature.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.Algebra.Module.Projective`: `Module.Projective`.
- `Mathlib.Algebra.Homology.HomologicalComplex`: `CochainComplex`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib's `SheafOfModules`, used in its expanded form.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Mathlib.CategoryTheory.Sites.Over`: `GrothendieckTopology.over`, `Sheaf.over`;
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, `over`, `Hom.over`, `overMap`,
  `overFunctorMap` (the dependency's exact Mathlib match, which needs no lean record).
- `Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral`:
  `CategoryTheory.siteConstantModuleFunctorGeneral` (constant presheaf followed
  by module sheafification).
- `Sheaf.CategoryTheory.SiteDerivedConstantModuleFunctor`:
  `CategoryTheory.siteConstantModuleFunctorGeneral_exact`,
  `CategoryTheory.siteModuleHasDerivedCategory`.
- `Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral`:
  `CategoryTheory.ringedOverFunctor_exactGeneral`,
  `CategoryTheory.ringedDerivedRestrictionSized`.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategoryFactors`.

The last three already landed definition nodes were added to `stmt_deps` to cite
these shared interfaces. No new node, dependency repair, or statement correction
is required. The imports also include the already stated proof dependencies:
right fractions, quasi-isomorphism calculi, cone acyclicity, exact faithful
forgetful functor, local surjectivity of epis, common refinement, and exact
sheafification. No import cycle was found; the parent module does not yet import
this item, and this item does not import its parent.

Edge cases checked before writing: the zero complex (any interval, identity
cover and zero map); a complex concentrated in one degree; the zero coefficient
ring; projective modules that are not free; an unbounded G or fraction complex
B; the one-object site; sites without points; and an empty covering of the final
object. All are admitted by the signature. The finite induction uses bounds only
on F, including its boundary differential equations. Empty covers are allowed by
the existential index type. No global K-projectivity of constant sheaves is
asserted. The equality has the correct source/target orientation: the source
comparison inverse goes first and the target comparison hom goes last.

Searches performed (2026-10-17):

- `msearch.py ... leanfinder`, query “A morphism from a bounded complex of
  constant finite projective modules in the derived category of sheaves is
  locally represented by a chain map”: eight hits including
  `DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective`,
  `CochainComplex.IsKProjective`, `isKProjective_of_projective`, and
  `IsKProjective.Qh_map_bijective`. These assume global projectivity/K-projectivity
  in an abelian category and do not give this local site theorem.
- `msearch.py ... loogle`, query `"CochainComplex", "Sheaf"`: zero hits.
- `msearch.py ... grep`, query `local.*(chain|actual)|perfect.*constant` in
  `Algebra/Homology`: nineteen hits concerning abstract localization and
  local attributes; none gives local actual representatives on ringed sites.
- `msearch.py ... leansearch`, query “On a ringed site, a morphism from a bounded
  complex of constant finite projective modules in the derived category locally
  comes from a morphism of complexes”: eight hits, including the single-projective
  vanishing theorem, `SheafOfModules.hasLimit`, `hasLimitsOfShape`, `Hom`,
  `isFinitePresentation`, `ProjectiveResolution.Hom.hom`, and
  `CochainComplex.isKProjective_of_projective`; no exact match.
- `rg` of the upstream `WeilConjectures` tree for this node id, local chain
  representability, and the prospective theorem name: no theorem match.
- `rg` of `lean/Sheaf` for the same patterns: the parent theorem's docstring
  cites this node, but no declaration states it. Scheme-specific chain-model
  comparison lemmas are different statements. Separate searches for termwise
  constant-complex and arbitrary-complex slice Q-comparison wrappers found no
  existing definition; the ringed restriction API only packages the degree-zero
  ring comparison, so the general comparison is supplied here directly from
  Mathlib's existing `mapDerivedCategoryFactors`.

Validation: `scompile.py Q113 lem-sfb-perfect-constant-local-chain-representative`
compiled this delivery as a sandbox file and as its library module with no error
or warning (7.6 s and 9.7 s). `autoImplicit false` is set; all variables and
universes are bound. The node record's signature is extracted by the project's
`stage2_delivery.py signature` reader. No node fault or disputed statement found.


## Second reading by Q113

I independently opened the sandbox node and Lean module, every statement dependency
record and its actual declaration, and the Stacks source at 09BD and 08FR(1),
including 08FN, 08FP and 08FQ. The paragraph before 09BD supplies the constant
realization; there is no hidden Noetherian, field, characteristic, or target-bound
hypothesis. The node is the stated commutative-ring, chosen finite-projective-model
specialization of 09BD, rather than the entire more general source lemma.

The node's objects, hypotheses and conclusion, in order:

1. A small site: `{C : Type u} [Category.{v} C]`, `(J : Precoverage C)` and
   `(_hJ : J.IsSiteForCoverings)`. I read `SiteCoveringAxioms.lean`: the last
   predicate is precisely the recorded interface for isomorphism coverings,
   bind composition and existence of covering pullbacks. Sheaves are on
   `J.toGrothendieck`. Verdict: matches the dependency, with independent site
   object and morphism sizes, and no assumption of all pullbacks.
2. Its final object X: `(X : C) (_hX : IsTerminal X)`. Verdict: matches; X is
   explicitly supplied, not a new chosen final object.
3. A commutative ring R: `(R : Type (max u v)) [CommRing R]`. Verdict: matches
   the node. The common coefficient universe contains the site data as required
   by the shared constant-module and module-sheaf APIs; it does not identify u
   and v or impose a finiteness or characteristic condition.
4. A cochain complex of R-modules: `(F : CochainComplex (ModuleCat R) ℤ)` with
   the displayed module universe `max u v`. I read the actual Mathlib
   `CochainComplex` definition, whose morphisms are commuting chain maps.
   Verdict: matches the integer-graded cochain object.
5. A finite interval outside which its TERMS vanish: `_hbounded` is
   `∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q → IsZero (F.X q)`.
   Verdict: exactly termwise boundedness, not merely bounded cohomology.
   Requiring an ordered interval loses no zero or empty-support case.
6. Every term finitely generated: `[∀ q : ℤ, Module.Finite R (F.X q)]`.
   I read Mathlib's class, `fg_top : (⊤ : Submodule R M).FG`.
   Verdict: matches finite generation, not finiteness of the underlying set.
7. Every term projective: `[∀ q : ℤ, Module.Projective R (F.X q)]`.
   I read its splitting of the canonical free-module surjection. Verdict:
   matches module projectivity, without assuming free terms or projective
   objects in the sheaf category.
8. The constant ring and termwise constant complex: the ring is
   `(constantSheaf J.toGrothendieck RingCat).obj (RingCat.of R)` and the source
   complex is `(constantModuleCochainFunctor J.toGrothendieck R).obj F`.
   The helper applies `siteConstantModuleFunctorGeneral` degreewise; that shared
   functor is the genuine constant module presheaf followed by sheafification
   along the constant-ring unit. Verdict: the recorded notions, not an
   arbitrary realization or a different coefficient ring.
9. An arbitrary complex G of modules over that ring sheaf: the binder is
   `G : CochainComplex (SheafOfModules ... ) ℤ`. I checked the dependency
   `ringedSiteModules` is transparently this same Mathlib category, and read
   the actual `SheafOfModules.overFunctor` definition. Verdict: matches;
   no boundedness, finite generation, injectivity or perfectness of G.
10. Localization Q and an arbitrary derived morphism: `DerivedCategory.Q` and
    `ψ : Q.obj (constant F) ⟶ Q.obj G`. The `siteModuleHasDerivedCategory`
    binders expand to the recorded Mathlib localization structures for the
    global module category and every slice, with independent morphism sizes
    `wS` and `wU`. Verdict: genuine localization at quasi-isomorphisms, with
    no assumption on ψ and no global K-projectivity hypothesis.
11. A covering of X: `∃ (I : Type (max u v)) (U : I → C)
    (f : ∀ i, U i ⟶ X), Presieve.ofArrows U f ∈ J X ∧ ...`.
    Verdict: an actual covering in the original precoverage, not only a
    covering sieve in its generated topology; no finite or nonempty cover
    restriction is added.
12. For each member, a chain map of the restricted complexes: `∀ i, ∃ a :
    (moduleCochainRestriction S (U i)).obj (constant F) ⟶
    (moduleCochainRestriction S (U i)).obj G`. The helper is the degreewise
    existing `SheafOfModules.overFunctor S (U i)`, on `S.over (U i)` and
    `J.toGrothendieck.over (U i)`. Verdict: exactly restriction to the
    localized ringed sites, with simultaneous chain equations in all degrees.
13. Its localization is the restriction of ψ: `Q.map a` equals source comparison
    inverse, then `(ringedDerivedRestrictionSized S (U i)).map ψ`, then target
    comparison hom. I read Mathlib's `mapDerivedCategoryFactors` signature
    `Q ⋙ F.mapDerivedCategory ≅ F.mapHomologicalComplex _ ⋙ Q` and its
    naturality equation. Verdict: correct source, target, and orientation;
    this is exactly `Q(a) = ψ|U_i` through the canonical identifications.
    The covering is chosen after ψ and before the memberwise maps, as required.

Edge cases: the empty cover is permitted because I has no `Nonempty` instance;
rank zero and the zero complex satisfy finite/projective hypotheses and can use
any ordered interval. Complexes concentrated in degree zero or one other degree
are included. The zero ring and every characteristic are included. No scheme is
assumed, so the empty-scheme instance is admitted when its site has the stipulated
final object. An empty category itself has no final object and is correctly
outside both statements. Nonfree finite projective terms, an unbounded G, sites
without points, and the one-object site are included. Site u and v and derived
morphism sizes wS and wU are explicitly bound; the coefficient-size convention
agrees with the shared dependency interfaces and the parent consumer.

Independent searches used different wording from the worker:

- `msearch.py ... leanfinder`, “After restricting to a cover, a map in the derived
  category from a finite complex of locally free summands is induced by a cochain
  morphism”: eight hits, including `CochainComplex.cm5b`, embedding-restriction
  lemmas and `DerivedCategory.left_fac_of_isStrictlyGE`. These concern abstract
  factorizations or degree restrictions, not local representatives on a site.
- `msearch.py ... loogle`, `"CochainComplex", "mapDerivedCategoryFactors"`:
  one hit, the shift-compatibility instance of Mathlib's existing factorization;
  no local-representative theorem.
- `msearch.py ... grep`, `local.*(homotopy|representative)|mapDerivedCategoryFactors`:
  25 homological-algebra hits, including the canonical comparison and its
  naturality; none supplies the site theorem.
- Independent `rg` over Mathlib homological algebra, upstream WeilConjectures,
  and the project's Lean found no declaration with the delivered theorem or
  helper names. Source/tag searches found `FiniteFreeEtaleLocalActual.lean`,
  which I opened: it requires a scheme's small etale site and finite FREE terms,
  uses a different module-sheaf encoding, and adds a local-null-homotopy clause.
  It cannot serve this arbitrary-site finite-projective statement. I also opened
  `PerfectConstantDerivedMapLocal.lean`: it concerns algebraic derived maps
  between two constant realizations and explicitly needs the present lemma.
  Neither is an exact existing declaration for this item. The general ringed
  restriction dependency packages the ring-in-degree-zero comparison only;
  the arbitrary-complex comparison helper here directly uses Mathlib's API.

The three helpers contain real canonical functor/isomorphism data. Their
`haveI` terms obtain proof instances from the already recorded exactness theorems,
not data from a postponed arbitrary existence claim. There are no new nodes or
repaired dependency modules to audit, and no statement correction or citer audit
is needed. The three added statement dependencies are already landed records
whose modules I opened; no duplicate notion is introduced. The six proof steps
in the theorem docstring agree with the node, including finite descending
induction and the two cone-component equations. Each declaration has its source
and blueprint tag. The only theorem has proof `sorry`; no auxiliary theorem was
proved, and no definition contains `sorry`.

Mismatch/change verdict: no mathematical, interface, or convention mismatch
found. I preserved the Lean and node, and appended this independent review only.
The only local command correction was rerunning compilation from the sandbox
working directory after an initial relative-path lookup failed. The completed
`scompile.py` run compiled the sole delivered module as sandbox and library
module cleanly (7.2 s and 6.2 s), with no errors or warnings. A source-text check
confirmed that `lean.statement` equals the whitespace-normalized file signature,
all four universe names are explicitly declared, and every Lean line is at most
100 characters. The original node differs only in `lean` and the three already
landed additions to `stmt_deps`; its mathematical statement and proof are intact.
