## Worker report

The module `Sheaf.CategoryTheory.RingedTripleResolutionFormulas` states
`CategoryTheory.ringedTripleResolution_formulas`, with its sole proof `by sorry`.
It supplies the real-data predicate `CategoryTheory.Functor.HasTripleResolutionFormulas`
packaging precisely this node’s full conclusion. It introduces no independent mathematical
notion, new node, axiom, dependency module, or statement correction. The helper is recorded
in `lean.declarations` and has its source and blueprint docstring. Its data is the explicit
conjunction and quantifiers, with no `sorry`.
The node changes only in `lean`. All variables and universes are explicitly bound;
`autoImplicit` is false. The section variables are part of the theorem's elaborated
signature, and its recorded `lean.statement` is the theorem signature verbatim.

### Hypotheses and objects

- The four small ringed sites are `C0` through `C3 : Type u`, their `SmallCategory`
  instances, `J0` through `J3`, and `A0` through `A3 : Sheaf Ji CommRingCat.{u}`.
- The morphisms `f`, `g`, `h` have exactly the recorded `RingedToposMorphism` type.
  In particular, they are geometric morphisms, not necessarily morphisms of the
  presented sites. The module direct images are their existing `.modules` fields.
- The categories are the recorded `ringedSiteModules.{u,u,u,u}` of the underlying
  ring sheaves, obtained by the existing `sheafCompose` forgetful functor. No second
  module category, abelian instance, or derived category is constructed.
- `HasDerivedCategory.{w}` on all four module categories supplies the ordinary
  unbounded derived categories and their localization functors `DerivedCategory.Q`
  and `DerivedCategory.Qh`; the latter is on the homotopy category. The comparison
  between these two localization presentations is handled by the dependency's
  `kInjectiveResolutionHomTarget` and `kInjectiveHomotopyImage`.
- `Rf`, `Rg`, `Rh`, `Rgf`, `Rhg`, `Rhgf`, their natural units `ηf` etc., and
  `hRf` etc. of type `IsRightDerivedFunctor` spell out the node's chosen total
  right-derived functors. The units are on cochain complexes, exactly as in the
  recorded pair-composition theorem. Underived composites are the composites of
  `.modules`, again exactly as in that theorem.
- `κgf`, `κhg`, `κh_gf`, `κhg_f` are the four natural comparison isomorphisms.
  The four hypotheses `hκgf`, `hκhg`, `hκh_gf`, `hκhg_f` are precisely the
  dependency's unit characterization of its normalized comparison. They specify
  the comparisons the node says to use; no associativity equation or preservation
  of K-injectives is assumed. The same presentation already appears in the
  downstream `RingedDerivedCompositionCocycle` module, but that module is neither
  imported nor used as a premise (avoiding a circular proof dependency).
- `I` is a K-injective complex on the first ringed site; `J` is K-injective on
  the second, and `K,T` on the third. Their `IsKInjective` instances are explicit.
- `j`, `k`, `t` have exactly the domains and codomains in the node, and their
  `QuasiIso` instances are the resolution hypotheses. There is no K-injectivity
  assumption on `f_*I` or `g_*J` and no assumption on preservation of K-injectives.

### Conclusions, clause by clause

Unfold the predicate in the main theorem to read all conclusions below.
The predicate’s additive-functor parameters `F`, `G`, `H` are instantiated by
`f.modules`, `g.modules`, `h.modules`. In the following explanation they mean the
corresponding degreewise functors. There is no file-local notation in the Lean file. Put `B = G(F(I))`, `C = G(J)`, `p = G.map j`, `w = p ≫ k`.

1. The first two conjuncts are `QuasiIso p` and `QuasiIso (p ≫ k)`.
2. `u` is a morphism between the images of `T,K` under `HomotopyCategory.quotient`.
   It is therefore a homotopy class of chain maps, not a chosen arbitrary map.
   The equation `DerivedCategory.Qh.map u =
   Functor.kInjectiveResolutionHomTarget t (𝟙 K) (Q.map w)` is exactly
   `Qu = (Qt)⁻¹ ≫ Qw`, with the dependency's canonical `Q`/`Qh` presentation
   identifications. `quotient.map t ≫ u = quotient.map w` is the homotopy
   `u ∘ t ≃ w`. The following universal clause gives uniqueness already from
   the displayed derived-map equation, hence in particular uniqueness with
   both conditions.
3. Seven coordinate isomorphisms `a,v,b,s,m,r,d` are existentially quantified,
   together with equations fixing their inverses. These implement precisely the
   canonical coordinates named in proof step 4 of the node. With `e_x = η_x⁻¹`:

   | Lean equation | Node coordinate |
   | --- | --- |
   | `a.inv = inv (Q.map j) ≫ ηf.app I` | `a = e_f ≫ Qj` |
   | `v.inv = ηgf.app I` | `v = e_gf` |
   | `b.inv = ηg.app J ≫ Rg.map a.inv` | `b = Rg(a) ≫ e_g` |
   | `s.inv = ηhgf.app I` | common source `s = e_hgf` |
   | `m.inv = ηh.app T ≫ Rh.map (inv (Q.map t) ≫ v.inv)` | `m = Rh(v ≫ Qt) ≫ e_h,T` |
   | `r.inv = ηhg.app J ≫ Rhg.map a.inv` | `r = Rhg(a) ≫ e_hg,J` |
   | `d.inv = ηh.app K ≫ Rh.map (inv (Q.map k) ≫ b.inv)` | common target `d = Rh(b ≫ Qk) ≫ e_h,K` |

   All formulas in this table use Lean's left-to-right `≫` order. Inverse
   equations avoid requiring an additional invertibility hypothesis on each
   derived unit. Existence of these isomorphisms is asserted by the theorem;
   their inverses, and hence the isomorphisms themselves, are determined by
   the equations. They are not unconstrained coordinate choices.
4. `s.inv ≫ κh_gf.hom.app (QI) ≫ m.hom = Q.map (H.map t)` gives the
   `κ_{h,gf}` factor in the required coordinates.
5. `m.inv ≫ Rh.map (κgf.hom.app (QI)) ≫ d.hom =
   h.modules.kInjectiveHomotopyImage u` is the `Rh(κ_{g,f})` factor.
   The helper from the recorded dependency is exactly localization of the
   degreewise `h_*` image of the homotopy class; no representative is chosen.
6. `s.inv ≫ κhg_f.hom.app (QI) ≫ r.hom = Q.map (H.map (G.map j))`
   gives the `κ_{hg,f}` factor.
7. `r.inv ≫ κhg.hom.app (Rf.obj (QI)) ≫ d.hom = Q.map (H.map k)`
   gives the `κ_{h,g}` factor after the identification induced by `j`.
8. The next conjunct composes the first two factors, giving the full alpha
   path `Q(h_*t) ≫ Q(h_*u)` in exactly the common `s,d` coordinates.
9. The next conjunct composes the other two factors, giving the full beta
   path `Q(h_*g_*j) ≫ Q(h_*k)` in the very same `s,d` coordinates.
   Lean's functor composition evaluates strictly on objects and morphisms,
   so the suppressed associator contributes an identity component here.
10. The theorem is universal in `j,k,t`. Its penultimate clause also states
    the canonical intermediate transition for every `t'` and its canonically
    normalized coordinate `m'`: `m.inv ≫ m'.hom` is the image of the unique
    class `z` with `Qz = (Qt)⁻¹ ≫ Qt'`, using the recorded helper.
11. Its last clause covers simultaneous arbitrary changes `j',k'`, including
    different resolution objects `J',K'`. Coordinates `a',b',d'` are fixed by
    precisely the same equations. `d.inv ≫ d'.hom` is the image of the unique
    class lifting `(Qk)⁻¹ ≫ (b.inv ≫ b'.hom) ≫ Qk'`. This is the canonical
    final-target transition from proof step 8. Because all full-path and
    factor formulas use these coordinate isomorphisms, they transform by
    these transitions; intermediate transitions cancel in full paths.

### Dependency declarations read and used

- `Sheaf.CategoryTheory.RingedToposMorphism`:
  `CategoryTheory.RingedToposMorphism` and its `.modules`, `.additive` fields.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules` (the existing Mathlib `SheafOfModules` category).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `HasDerivedCategory`, `DerivedCategory`, `.Q`, `.Qh`, `.quotientCompQhIso`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`; resolutions use the existing `QuasiIso` class.
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`:
  `CategoryTheory.ringedToposDerivedPushforwardComposition`. Its actual signature
  returns existential derived pairs and a unique normalized comparison, and its
  normalization includes the quasi-isomorphism of `g_*j`. Our binders use exactly
  those pairs and the unit characterization of those comparisons.
- `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`:
  `CategoryTheory.Functor.kInjectiveResolutionHomTarget`,
  `.kInjectiveHomotopyImage`, `.kInjectiveDerivedMapComputation`,
  `.kInjectiveDerivedResolutionTransition_computation`,
  `.kInjectiveDerivedResolutionTransition_laws`, and
  `.kInjectiveDerivedResolutionTransition_naturality`.
- Proof import `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`:
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`.
- Proof import `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `.rightDerivedFunctorOfQuasiIsoResolutions`, its unit, universal property,
  unit invertibility on K-injectives, and `.rightDerivedFunctorOfQuasiIsoResolutionsObjIso`.
- Proof import `Mathlib.Algebra.Homology.DerivedCategory.KInjective`:
  `CochainComplex.IsKInjective.Qh_map_bijective`.

### Sources and edge cases

Read Stacks `sites-cohomology.tex`, lemma-derived-pushforward-composition, Tag 0D6E
(lines 4010ff), and the current main-20261015 blueprint `fix-prop-adjunctions.proof.md`,
Step 3. Stacks supplies the pair-composition theorem; this node's explicit triple
formulas are the agent extraction already recorded in its source and proof_origin.
The declaration docstring carries all eight proof steps and their named dependencies.

Checked `I=0`, identity morphisms, identity resolutions wherever their sources are
K-injective, identical primed/unprimed resolutions, and the choice `t=w` when
`g_*j` and `k` are supplied. The latter uses `T=K`, and the unique class is the
identity. For identical primed/unprimed resolutions the transitions are identities.
Empty sites and zero commutative ring sheaves are not excluded. The setup allows
identity-underlying-topos coefficient changes such as `ℤ → 𝔽_p`: no flatness,
faithfulness, or K-injective preservation is imposed. All degrees are `ℤ` and
there is no boundedness condition. The chosen localization universe `w` is not
identified with `u`. No node fault or statement dispute was found.

### Searches

All service searches were made with the prescribed `msearch.py O3
lem-pur-ringed-triple-resolution-formulas` wrapper.

- LeanFinder query: `Compute two triple unbounded derived pushforward comparisons
  using common K-injective resolutions`. Eight hits included
  `Functor.mapDerivedCategoryFactors`,
  `LocalizerMorphism.rightDerivedFunctorComparison`,
  `LocalizerMorphism.rightDerivedFunctorComparison_fac`,
  `Functor.rightDerived_map_eq`, `InjectiveResolution.rightDerived_app_eq`,
  and injective-resolution comparison/naturality lemmas. None states these
  four factors and two paths for unbounded ringed-topos module direct images.
- Loogle query: `CategoryTheory.Functor.IsRightDerivedFunctor,
  CategoryTheory.Functor.rightDerivedUnique`. One hit, `Functor.rightDerivedUnique`:
  abstract uniqueness of right derived functors, not the node's formulas.
- Mathlib grep query: `triple|rightDerived.*comp_assoc`, under
  `CategoryTheory/Localization`: zero hits.
- LeanSearch query: `Two triple direct image derived comparisons computed on common
  K-injective resolutions`. Eight hits: natural-number derived functors and
  injective-resolution computations, including `Functor.rightDerived_map_eq`
  and `InjectiveResolution.isoRightDerivedObj_inv_naturality_assoc`. No match.
- `rg` on `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for `ringedTripleResolution|lem-pur-ringed-triple-resolution-formulas|
  triple.*[Rr]esolution|[Rr]esolution.*triple` found no existing statement.
  Broad normalized-comparison searches found the pair-composition theorem,
  `NormalizedDerivedComparisonCommonResolution`, and the downstream
  `RingedDerivedCompositionCocycle`; these state distinct assertions. The
  downstream theorem gives the cocycle equality, not these component formulas.
- `grep -rn 'lem-pur-ringed-triple-resolution-formulas' lean/WeilConjectures`:
  zero hits. Also searched normalized composition/cocycle patterns throughout
  the upstream derived-category and six-functor directories. No existing match.

### Validation

An initial expanded signature passed once in 55.5 seconds but timed out on repetition.
Profiling showed the cost of repeatedly elaborating concrete module-sheaf categories.
The conclusion was therefore factored, unchanged, into the real-data predicate over
additive functors. The final module is compiled with the prescribed server-only
`scompile.py`, under the unchanged 60-second limit. No local compilation was run.
The delivery dry run and final push are recorded by the prescribed wrapper.

## Second reading by O3

Author's self-check, with the complete node and Lean module open; the maintainer
performs the independent review, as required by this dispatcher's brief.

I checked every hypothesis and conclusion against the mapping above, unfolding
`Functor.HasTripleResolutionFormulas`. Its generic category parameters specialize
exactly to the existing module-sheaf categories; it proves nothing about arbitrary
additive functors and is only a definition of the displayed conjunction. In particular,
`d` has codomain `Q(h_*K)` and source `Rh(Rg(Rf(QI)))` in both path equations;
`m` is used only for the first path and `r` for the second. The middle lift uses
`t` and the resolution `w` into `K`; its two equations are the required derived
fraction and homotopy. The second factor is computed by the existing homotopy-image
helper, whose full definition includes the canonical `Q`/`Qh` identifications.
I checked both transition orientations: `m.inv ≫ m'.hom` is from `Q(h_*T)`
to `Q(h_*T')`, and `d.inv ≫ d'.hom` from `Q(h_*K)` to `Q(h_*K')`.
The lift for the latter uses `k,k'` and `b.inv ≫ b'.hom`, so it covers changes
of `j` as well as changes of `k`. The unit equations do not assume the desired
triple equality. No correction or missing dependency is needed. Nothing is proved;
the single theorem has exactly one `sorry` and a complete eight-step proof docstring.
