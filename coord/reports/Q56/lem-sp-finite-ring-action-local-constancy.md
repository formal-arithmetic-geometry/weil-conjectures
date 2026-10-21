## Worker report

H3 repair of returned head a05421e5cef3. The module
`Sheaf.CategoryTheory.FiniteRingActionLocalConstancy` states
`SheafOfModules.finite_ring_action_local_constancy`, with its only proof `sorry`.
The saved packet's initial dry run passed, but its `SmallCategory C` binder still
excluded the sole citer's pro-etale site. That binder has been repaired.
The natural-language node statement is unchanged. Only its `lean` record and its
added landed constant-module dependency differ from the live read-clone node.

Clause-by-clause correspondence:

- The small site's objects and morphisms form sets independently:
  `{C : Type uC} [Category.{vC} C]`. Actual covering families are encoded by
  `(J : Precoverage C) (hJ : J.IsSiteForCoverings)`, exactly the recorded
  `def-weil-pbc-sites-and-cohomology` predicate. No equality of universes is imposed.
- `(Λ : Type (max uC vC)) [CommRing Λ] [Finite Λ]` is the finite commutative
  ring in an ambient universe containing both site universes, as in proof step 1.
- The constant commutative ring sheaf is
  `(constantSheaf J.toGrothendieck CommRingCat.{max uC vC}).obj (CommRingCat.of Λ)`.
  Apply `sheafCompose ... (forget₂ CommRingCat RingCat)` for its underlying ring.
  This is exactly the coefficient presentation used by the pro-etale citer.
- `F : CategoryTheory.ringedSiteModules.{max uC vC} (...)` is a sheaf of
  modules over that ring, using the existing transparent Mathlib abbreviation.
- The underlying sheaf of sets is obtained by `SheafOfModules.toSheaf _` and
  `sheafCompose ... (CategoryTheory.forget AddCommGrpCat.{max uC vC})`.
- The underlying finite local constancy hypothesis is `hF`: for every `U : C`
  there is `S : Presieve U` with `S ∈ J U`; for each member `f : V ⟶ U`,
  `∃ X : Type (max uC vC), Finite X ∧ Nonempty (...)` supplies an isomorphism
  between the restricted underlying set sheaf and the constant finite-set sheaf
  on `J.toGrothendieck.over V`.
- The conclusion uses the same actual J-cover quantifiers for every object.
  Each member supplies `M : ModuleCat.{max uC vC} Λ` with `Finite M` (finite
  underlying set, rather than finite generation), and an isomorphism of module
  sheaves `F.over V ≅ ((commutativeSiteConstantModuleFunctor
  J.toGrothendieck Λ).obj M).over V`. Both sides are modules over precisely
  the restricted forgotten constant commutative ring sheaf.
- The constant model uses the already-landed
  `CategoryTheory.commutativeSiteConstantModuleFunctor`, whose full construction
  was read: `siteConstantModulePresheafGeneral` gives value M and identity
  restriction maps, followed by `PresheafOfModules.sheafification` along
  `realizationRingUnit`, the commutative ring sheafification unit with commutativity
  forgotten. There is no arbitrary action, map or choice. Slice compatibility is
  `lem-cbc-sieve-slice-sheafification`, as in the unchanged node proof.
- No point, inhabited object, nonempty covering, final object, nonzero ring or
  global pullback instance is assumed. Site and coefficient universes are bound
  explicitly and `autoImplicit` is false. Mathlib supplies the required
  sheafification and local-bijection instances at the ambient maximum; no added
  sheafification hypotheses or universe equalities are needed.

Dependency declarations used (full declarations/docstrings read):

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`:
  `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules` = `SheafOfModules`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`:
  `SheafOfModules.overFunctor`, `SheafOfModules.over` and their existing
  restrictions on module morphisms and relocalizations; `Sheaf.over` and
  `GrothendieckTopology.over` give the underlying sheaf and site restrictions.
- `Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor`:
  `CategoryTheory.commutativeSiteConstantModuleFunctor`, `realizationRingUnit`
  and `realizationModules`; its public dependencies provide
  `siteConstantModulePresheafGeneral`. The owning landed node
  `def-sfb-site-derived-constant-module-functor` is added to `stmt_deps`.
  `realizationRingIso` and `commutativeSiteConstantModuleFunctor_transport`
  also record canonical compatibility with constant RingCat sheafification.
  Reuse resolves the return without a duplicate helper or dependency repair.

The unchanged proof imports are `LocallyBijective`, `CoverLifting`, module-presheaf
`Sheafification`, `PreservesSheafification`, and upstream
`WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`.
The latter is a proof import; its stronger precoverage assumptions are not added
as theorem hypotheses. The module docstring retains the complete six-step proof.

Sources: Stacks Project `sites-modules.tex`, Tag 093S
(`lemma-morphism-locally-constant`, proof omitted), `sites.tex` Tag 00WK,
and the current `main-20261015` blueprint scalar-extension proof paragraph (2).
The project's Lean 4 skill and `coord/pefw-upstream-framework.md` were consulted.

Edge cases checked: an empty site makes both objectwise conditions vacuous;
empty J-covers are allowed; a finite local model X may be empty (the zero-section
representation then permits an empty refinement); the zero ring is allowed;
labels need not inject into sections on empty-covered objects. On the one-point
site this reduces to the finite module itself. In addition, the repaired signature
admits objects in `Type (t+1)` and morphisms in `Type t`, including `T.ProEt`.

Searches actually run (all via the prescribed wrapper or read-only source `rg`):

- LeanFinder: "A finite ring action on a finite locally constant sheaf on an arbitrary
  small site is locally constant". Eight hits, including
  `CompHausLike.LocallyConstantModule.functor` and condensed module constructions;
  these are special sites, not the statement here.
- Loogle: `CategoryTheory.Sheaf.IsConstant, SheafOfModules`. Zero hits.
- Mathlib grep: `isConstant_of_forget|[Ll]ocally[Cc]onstant` in `CategoryTheory/Sites`.
  Two hits in `ConstantSheaf.lean` (212, 233); these need full and faithful constant
  functors, which are not hypotheses of this node.
- LeanSearch: "A sheaf of modules over a finite ring is finite locally constant if its
  underlying set sheaf is finite locally constant". Eight hits, including
  `SheafOfModules`, `SheafOfModules.IsFiniteType` and `Scheme.Modules`; none is the
  arbitrary-site finite-action statement.
- `rg` in `lean/WeilConjectures` for finite/local-constant terms and the node id,
  and in `lean/Sheaf/CategoryTheory` for constant module and local constancy terms.
  The node id has no existing match. Relevant declarations were opened:
  `CategoryTheory.Sheaf.exists_mem_forall_isConstant_over_of_forget` in
  `WeilConjectures.CategoryTheory.Sites.ConstantForget` starts with a globally
  constant finite underlying set sheaf, and concludes local constancy without a
  finite-module model in its statement, so it is not an exact match.
  `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.of_forget` in
  `WeilConjectures.ConstructibleSheaf.OfForget` is restricted to a scheme's etale
  site and uses stalks/nonempty members; it is not the arbitrary-site statement.
  Existing `SheafOfModules.IsFiniteTypeLocallyConstant` uses finitely generated
  models; our statement explicitly demands finite underlying sets. The candidate new theorem name was also searched
  in both project trees and `dag/lean_names_upstream.json`, with no collision.


Repair searches: read-only `rg` for `siteConstantModule`, `strictPerfectConstant`,
and `commutativeSiteConstantModuleFunctor` located the already-landed independent
universe construction and its owning DAG record. Its source, coefficient unit,
constant presheaf, module sheafification and coefficient-transport declarations
were read in full. The previous strict-perfect constructor requires coinciding
site universes, so the repaired statement reuses this existing general interface.

Validation: the repaired module compiled cleanly through `scompile.py` as sandbox
and library module (1.8 s and 1.6 s). A separate consumer probe checks specialization
on the actual pro-etale precoverage/topology of `T : Scheme.{t}`, coefficient ring
`ULift.{t+1,t} A`, and exactly the forgotten constant CommRingCat ring sheaf of
`proEtaleDerivedCategory T A`. It applies the delivered theorem directly to F and
its local-constancy hypothesis, including the finite module conclusion.
The final probe compiled without warnings (2.3 s sandbox, 2.4 s library).
The scratch probe is removed from the packet; its exact contents follow:

```lean
module
import Sheaf.CategoryTheory.FiniteRingActionLocalConstancy
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
set_option autoImplicit false
universe t
open CategoryTheory
example (T : AlgebraicGeometry.Scheme.{t}) (A : Type t) [CommRing A] [Finite A]
    (hJ : (AlgebraicGeometry.Scheme.ProEt.precoverage T).IsSiteForCoverings)
    (F : SheafOfModules.{t + 1}
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj
          ((constantSheaf (AlgebraicGeometry.Scheme.ProEt.topology T) CommRingCat.{t + 1}).obj
            (CommRingCat.of (ULift.{t + 1, t} A)))))
    (hF : ∀ U : T.ProEt, ∃ S : Presieve U, S ∈ AlgebraicGeometry.Scheme.ProEt.precoverage T U ∧
      ∀ (V : T.ProEt) (f : V ⟶ U), S f →
        ∃ X : Type (t + 1), Finite X ∧
          Nonempty
            ((((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology T)
                (CategoryTheory.forget AddCommGrpCat.{t + 1})).obj
              ((SheafOfModules.toSheaf _).obj F)).over V) ≅
              (constantSheaf ((AlgebraicGeometry.Scheme.ProEt.topology T).over V)
                (Type (t + 1))).obj X)) :
    ∀ U : T.ProEt, ∃ S : Presieve U, S ∈ AlgebraicGeometry.Scheme.ProEt.precoverage T U ∧
      ∀ (V : T.ProEt) (f : V ⟶ U), S f →
        ∃ M : ModuleCat.{t + 1} (ULift.{t + 1, t} A), Finite M ∧
          Nonempty (F.over V ≅
            ((commutativeSiteConstantModuleFunctor
              (AlgebraicGeometry.Scheme.ProEt.topology T) (ULift.{t + 1, t} A)).obj M).over V) :=
  SheafOfModules.finite_ring_action_local_constancy
    (AlgebraicGeometry.Scheme.ProEt.precoverage T) hJ (ULift.{t + 1, t} A) F hF
```


## Second reading by Q56

The dispatcher forbids sub-agents; independent review belongs to the maintainer.
On a separate reread of the final node, source and module, I checked every binder,
actual covering quantifier, underlying set sheaf, finite model, restriction and
coefficient ring. The saved SmallCategory restriction was the mismatch: it is now
`Category.{vC} C`, with coefficients and models in `max uC vC`. The constant module
functor now uses the existing commutative coefficient presentation and independent
site universes. No source statement correction is needed. No claim of an independent
second worker review is made.
