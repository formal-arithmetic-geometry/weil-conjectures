## Worker report

The module states functoriality for the resolution based cohomology map. `moduleCohomologyFMap_independent` renders clause (1), asserting equality for every two choice systems and every `p`. `moduleCohomologyFMap_comp` renders clause (2), with the Mathlib `pushforwardComp` comparison identifying the composite pushforward. `moduleCohomologyFMap_source_naturality` and `moduleCohomologyFMap_target_naturality` render the two identity special cases for source and target module morphisms. `moduleCohomologyPullback_comp` renders the pullback clause using `tensorPullback` and the unit compatibility equation for `c`. `moduleCohomologyFMap_restriction` renders the open restriction clause, including the sectionwise restricted map and the cohomology equality.

The declarations used are `Sheaf.AlgebraicGeometry.ModuleCohomologyFMap`, declarations `AlgebraicGeometry.Scheme.Modules.ModuleCohomologyFMapData`, `moduleCohomologyFMap`, `moduleCohomologyPullback`, and `moduleCohomologyRestriction`; `Sheaf.AlgebraicGeometry.TensorPullback`, declaration `AlgebraicGeometry.Scheme.Modules.tensorPullback`; `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`, declaration `exists_tensorPullbackAdjunction`; Mathlib `AlgebraicGeometry.Scheme`, declaration `Scheme`; Mathlib `AlgebraicGeometry.Modules.Sheaf`, declarations `pushforwardComp`, `pushforwardCongr`, `restrictFunctor`, and `restrictAdjunction`; and Mathlib `AlgebraicGeometry.Restrict`, declarations `Scheme.Hom.resLE` and `Scheme.Hom.resLE_comp_ι`.

Edge cases checked: `p = 0`; identity morphisms in the two naturality clauses; empty and maximal opens (`V = ⊥`, `V = ⊤`) through the unrestricted `V : Z.Opens`; and zero modules, which are allowed by the module-category binders. Universes are shared explicitly by `Scheme.{u}` and `AddCommGrpCat.{u}`.

Searches: LeanSearch for “Functoriality of maps on cohomology of sheaves of modules along scheme morphisms” (service unavailable); Loogle for `AlgebraicGeometry.Scheme.Modules.pushforwardComp` (found `pushforwardComp` and its app lemmas); grep of Mathlib `AlgebraicGeometry/Modules` for `cohomologyFMap|pushforwardComp|restrictFunctor` (found the pushforward and restriction declarations); `rg` of the source and `lean/Sheaf` for cohomology-map functoriality (no existing theorem for this node).

No statement correction or `STATEMENT-DISPUTED` flag.

## Earlier second reading (a previous round; superseded)

The file and node were reread together. Each source hypothesis is represented by explicit scheme, module, morphism, open, and degree binders; the composition and restriction clauses retain the canonical pushforward comparisons and unit equations. The only implementation split is into six declarations listed in the node's `lean.declarations`, one per clause, all with proofs `sorry`.

## Second reading by R1

Independent reading of the node, all six theorem signatures, the dependency declarations,
and Stacks Cohomology of Sheaves, section-functoriality, lemma-functoriality (01F8),
equation-functorial (01FA), and remark-explain-arrow (01FB). The repository lacks the
Stacks checkout; I read the available local Stacks cohomology.tex in c1-stacks-review.
The source assumes arbitrary ringed spaces, arbitrary module sheaves, and bounded below
complexes for the derived construction. The node specializes to schemes and modules in
degree zero; it assumes no finiteness, separation, flatness, or characteristic condition.

Object, hypothesis, and conclusion checklist:

1. Schemes X, Y and scheme morphism h: `{X Y : Scheme.{u}} (h : X ⟶ Y)`.
   `Scheme` and its morphisms are the dependency def-pc-scheme's Mathlib declarations.
   Verdict: same objects, no extra geometric hypotheses.
2. O_Y-module G, O_X-module F, and h-map φ: `{G : Y.Modules} {F : X.Modules}`
   and `(φ : G ⟶ (pushforward h).obj F)`. Mathlib's `Scheme.Modules` is exactly
   `SheafOfModules.{u} X.ringCatSheaf`; pushforward evaluates at inverse images and
   restricts scalars using the scheme's structure map. Verdict: exact.
3. Degree p ≥ 0 and H^p on O-module sheaves: `(p : ℕ)` and
   `RingedSpace.moduleCohomology X.toRingedSpace p`, viewed in `AddCommGrpCat` by
   `forget₂`. I read PQFCohomology and RingedSpaceModuleCohomology: this is the right
   derived functor of module-valued global sections, not the alternative abelian-sheaf
   Ext definition `Scheme.Modules.H`. Verdict: exact underlying cohomology groups.
4. Clause (1), every two choice systems: `C C' : ModuleCohomologyFMapData h G F φ`
   and `C.map p = C'.map p` in `moduleCohomologyFMap_independent`. I opened the
   dependency ModuleCohomologyFMap: I/J are injective resolutions, K is the nonnegative
   complex of injectives, lambda is a quasi-isomorphism, and β has the specified
   augmentation. The extra comparison a is fixed componentwise to the identity on
   sections; invertible supplies the proven-in-the-source invertibility of H(μ).
   `Data.map` is precisely iota_J, H(Γβ), H(μ) inverse, iota_I inverse, with forgetful
   homology comparisons. The iotas are Mathlib `isoRightDerivedObj`, whose signature
   and naturality I read. Verdict: arbitrary systems, exactly the node's formula.
5. Clause (2), X → Y → Z, modules H/G/F and maps ψ/φ: the binders of
   `moduleCohomologyFMap_comp` introduce all these. The composite module map is
   `ψ ≫ (pushforward k).map φ ≫ (pushforwardComp h k).hom.app F`; the last factor
   is the canonical comparison k_*h_* → (h ≫ k)_*, whose section components are
   identities in Mathlib. The conclusion equates its cohomology map with
   `moduleCohomologyFMap k ψ p ≫ moduleCohomologyFMap h φ p`. Verdict: exact order
   of composition; the composite's being an (h ≫ k)-map is already its Lean type.
6. Identity special cases, u:G' → G and v:F → F':
   `moduleCohomologyFMap_source_naturality` uses `a : G' ⟶ G` and the map of
   `RingedSpace.moduleCohomology Y.toRingedSpace p`; target naturality uses
   `b : F ⟶ F'` and the corresponding X functor. Their equations have exactly
   the node's two compositions. Verdict: both clauses present without extra hypotheses.
7. Pullback special case: `moduleCohomologyPullback_comp` uses `tensorPullback`
   for h, k, and h ≫ k. I read TensorPullback: it is the sheafified tensor formula,
   not Mathlib's alternative implementation. `c` has the stated comparison type;
   `hc` is exactly the node's unit compatibility, inserting pushforwardComp to type
   the canonical identification. The units come from `exists_tensorPullbackAdjunction`,
   which pins them to the sectionwise tensor unit. The composite adjunction Hom
   bijection determines c uniquely from hc, so this binder does not assume an
   additional property of h or k. The conclusion ends with H^p(c), as required.
   Verdict: exact canonical-comparison formulation.
8. Clause (3), open V, W = k inverse-image V, and restricted morphism:
   `(V : Z.Opens)`, `k ⁻¹ᵁ V`, and `k.resLE V (k ⁻¹ᵁ V) le_rfl`.
   `ψV` has source `(restrictFunctor V.ι).obj H` and target the restricted direct
   image of `(restrictFunctor (k ⁻¹ᵁ V).ι).obj G`. I read restrictFunctor,
   restrictAdjunction, pushforwardCongr, and their component formulas. The first
   conjunct is the module restriction square, transported along `resLE_comp_ι`.
   On an open T of V its unit component is restriction from T to itself, so the
   square forces ψV_T to be ψ_T under the canonical section identifications.
   Thus the existential does not permit an arbitrary map satisfying only the
   cohomology equation; the adjunction Hom bijection also gives uniqueness.
   The second conjunct states the required cohomology square for every p.
   ψV is chosen before `∀ p`, matching a single sectionwise map in every degree.
   Verdict: exact restricted map and all degrees, with no extra conclusion.

Edge cases: p = 0 is included by ℕ. Identity scheme morphisms and zero modules are
unrestricted. Empty schemes and V = ⊥ are allowed; V = ⊤ is also allowed. No index
set is quantified (the complex indexing ℕ encodes the source's zero negative degrees).
There is no nonempty, Noetherian, finite, field, or characteristic binder. The parameter
u is arbitrary and the scheme/module categories consistently use it; larger objects
can be placed in a common larger universe. `autoImplicit false` and explicit `universe u`
leave no implicit variable or universe unbound.

Independent searches: LeanFinder query “cohomology map associated to a morphism into
the direct image of a module sheaf respects composition” returned group-cohomology
composition and ordinary section-map lemmas, not this statement. Loogle query
`CategoryTheory.InjectiveResolution.isoRightDerivedObj` found the standard resolution
comparison and naturality lemmas, which are already used by the dependency. LeanSearch
query “induced cohomology maps on sheaves of modules commute with restriction to an open
subset” was unavailable (HTTP internal server error); no absence verdict is based on it.
The msearch grep for `moduleCohomologyFMap|moduleCohomologyPullback|moduleCohomologyRestriction`
returned no hits. Independent rg of Mathlib algebraic geometry and upstream cohomology
for `cohomology.*map|map.*cohomology|rightDerived.*comp`, and of upstream/project Lean
for `cohomology.*[Ff]unctorial|cohomology.*[Rr]estrict`, found upstream fixed-scheme maps
using the alternative H and project étale functoriality, neither the present O-module
f-map statement. The upstream name table has no match for this node. No duplicate found.

No H3/H4 mismatch was found; no Lean or node change is needed. There are no new nodes,
dependency modules, statement correction, or disputed flag in this delivery. Every
declaration has the source and blueprint docstring; their proof narrative covers all
eight node steps (homotopy uniqueness, three independence comparisons, pushforward
identification, composition, special cases, restriction). All six proofs remain `sorry`,
and there is no definition in this module. The sole import supplies the used definitions.
The node's `lean.statement` is verbatim the primary signature, and its `declarations`
lists all six clauses. Second reading changes only this detailed review report.
