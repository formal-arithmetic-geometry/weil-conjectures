## Worker report

The module `Sheaf.Paper.SupportedLatticeHomReductionTower` states
`AlgebraicGeometry.ProEtale.SupportedLatticeHom.supported_lattice_hom_reduction_tower`.
Its only postponed proof is that named theorem. `Assertions` is a completely written
proposition, and every tower helper has actual data. No definition is chosen from a
mere existence theorem and no private coefficient, support, tensor, or completion notion
is introduced. The helper declarations specialize and assemble the existing operations
for the one supported lattice tower in this node.

Source checked: main-20261015, sec-six-functors-basics,
`sk-lem-uniform-constructible-ext/sk-lem-uniform-constructible-ext.proof.md`, especially
Lattices and Integral targets. Also read the local Stacks sites-cohomology.tex,
`lemma-RGamma-commutes-with-Rlim` (Tag 0D6K). The theorem docstring carries the ten
proof steps of the DAG, including the exactness, completeness, products, and Hom steps.

Hypothesis-by-hypothesis correspondence:

- The prime ell is `l : ℕ` with `[Fact l.Prime]`.
- The finite coefficient extension is `E : Type u`, `[Field E]`,
  `[Algebra (Padic l) E]`, `[FiniteDimensional (Padic l) E]`.
  The recorded `DerivedNakayama.integerRing l E` is the continuous condensed integer
  ring for its spectral absolute value. The uniformizer and its quotient ideals are
  the existing `Padic.coefficientExtensionUniformizer` and `coefficientExtensionIdeal`.
- The base field, positive characteristic, and prime inequality are `k`, `[Field k]`,
  `p`, `[Fact p.Prime]`, `[CharP k p]`, and `hp : p ≠ l`.
- The standing separated finite-type k-scheme is `X` with `X.Over (Spec (.of k))`,
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on its structure map.
  Every other scheme has its induced structure map through the displayed immersion
  to X. Closed and open immersions preserve separated finite type, so these binders
  express exactly the same setting without adding independently chosen k-structures.
  All displayed arrows are k-morphisms for these induced structures.
- The closed/open pair is `i : Z ⟶ X`, `j : V ⟶ X`, `[IsClosedImmersion i]`,
  `[IsOpenImmersion j]`, and `hij : Set.range i.base = (Set.range j.base)ᶜ`.
- The source stratum is `uS : S ⟶ Z` with `[IsOpenImmersion uS]`. Its locally closed
  extension is literally `extension l E i uS`, namely the ordinary `i_*u_!`.
- The target stratum is `h : B ⟶ X`, `v : T ⟶ B`, with `[IsClosedImmersion h]`
  and `[IsOpenImmersion v]`. Its extension is literally `h_*v_!`.
- The two lattices are `L : AdicCompletion.Modules l E S` and
  `M : AdicCompletion.Modules l E T`; `hL` and `hM` use the recorded
  `IsLisseCoefficientModule` without a fixed rank or a connectedness assumption.
- `Scheme.{u}`, pro-etale sheaves valued in `Ab.{u+1}`, and the existing standard
  `DerivedCategory` instances implement the recorded size convention. No bounded
  derived category or equality of site object and arrow universes is imposed.

Clause-by-clause correspondence, obtained by unfolding the public `Assertions`:

1. `AdicCompletion.ring l E Y` is R_Y. `finiteRing l E Y n` is A_(n+1),Y and
   `quotient l E Y n` is its actual quotient coefficient morphism. Index n : ℕ
   everywhere in this module means the strictly positive exponent n+1.
   `AdicCompletion.restrict` is termwise restriction on the derived categories.
2. `finiteQuotient T M n` is the ordinary quotient M/pi^(n+1), formed by ordinary
   extension of scalars. `finiteExtension` is its ordinary finite-coefficient h_*v_!,
   and `finiteDerivedExtension` places it in degree zero, giving N-bar_(n+1).
   `restrictionIso` and `levelRestrictionIso` are constructed canonical isomorphisms
   from its scalar restriction to `level`, not additional assumptions.
3. `finiteQuotientStep` is the quotient-induced map: it is the unique adjunction
   mate of the smaller quotient unit, transported by `ordinaryRestrictComp`.
   `quotientStep` restricts its scalars. `step` applies h_*v_! and the degree-zero
   functor. `projection` applies the same functors to the actual quotient unit.
   Thus neither the inverse system nor its maps are arbitrary inputs.
4. `stratumDual` is sheaf Hom from L to the regular module. The first conjunct
   says this dual is lisse, exactly finite locally free in the recorded terminology.
5. `target` is N in degree zero. The second conjunct is precisely the existing
   `IsDerivedComplete l E X (target ...)` predicate, with its canonical completion
   augmentation on a K-flat representative.
6. The third conjunct gives `e n : level n ≅ integralLevel N n`. The latter is
   Res_n of the existing derived scalar extension of N. The two following equations
   assert compatibility with the actual quotient transitions and the adjunction
   reduction units, respectively. This states the canonical reduction comparison,
   not merely an isomorphism between unrelated objects.
7. `supportFunctor` is T_R: the recorded derived closed support, then exact u*, then
   the recorded derived relative tensor with L-dual in degree zero. Its support
   uses `formalClosedSupport`, the exact i* ker(id -> j*j*) construction, and not
   an arbitrary support functor. `transformedTarget` is F and `transformedLevel` is F_n.
8. `sectionsLevel` is B_n and `sectionsStep` is its quotient-induced transition.
   Both use the unchanged `stratumRGamma`, recorded by the new definition node
   `def-sfb-stratum-hom-sections-dual`. It is literally the total unbounded right
   derived functor of Hom from the regular module into Ab. The exact reconciliation
   with the cited ringed-site H0/RΓ convention is given below under “New nodes”.
9. The last main conjunct first provides the three products as conclusion data,
   not as extra hypotheses. It then gives pN, deltaN and their distinguished
   `IsDerivedLimitTriangle`, with every projection equal to `projection n`.
   This is N ≃ Rlim N_n through its specified reduction cone.
10. `eF` is the product comparison for T_R and `eB` the product comparison for RΓ.
    Both are normalized by every product projection. The next two
    `IsDerivedLimitTriangle` clauses have first maps `T_R.map pN ≫ eF.hom` and
    `RΓ.map (...) ≫ eB.hom`. Their boundary maps use exactly the inverse product
    comparisons and the canonical `commShiftIso`. These clauses explicitly say
    applying T_R and RΓ gives the asserted Roos triangles, and in particular
    F ≃ Rlim F_n and RΓ(S,F) ≃ Rlim B_n.
11. The next two clauses are isomorphisms in `DerivedCategory Ab.{u+1}`:
    RHom(Q,N) ≅ RΓ(S,F), and RHom(Q,N_n) ≅ B_n for every n. Global Hom is the
    existing `stratumGlobalRHom`; Q is literally the degree-zero i_*u_!L.
12. For every D with `IsDerivedLimit sectionsStep D`, the next clause states
    RHom(Q,N) ≅ D in the derived category, followed by an isomorphism in Ab between
    `preadditiveCoyoneda.obj (op Q)` on N[q] and H^q(D). The final clause states
    H^q(B_n) ≅ Hom(Q,N_n[q]), again in Ab. `preadditiveCoyoneda` supplies the actual
    abelian group of derived morphisms, which is exactly the node's definition of Ext.
    Both q binders range over all integers. The existence of D is already provided
    by the preceding RΓ(S,F) Roos triangle, so this universal clause is not vacuous.

Dependency declarations read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `CondensedRing.compactificationOverField` describes the setting; no compactification
  is needed for these explicit closed/open composites.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: coefficient extension
  definitions and `Padic.finite_coefficientExtensionRing` (proof input).
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`, and their canonical ring structures.
- `Sheaf.Paper.DerivedNakayamaResolution`: `integerRing`, `quotientRing`,
  `reductionRingSheaf`, and `reductionRing` use continuous sections and quotient topology.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` supplies the
  unbounded derived-functor convention; the existing upstream rightDerivedFunctor
  specializes it to these Grothendieck abelian internal module categories.
- `def-weil-size-convention` is a metatheoretic convention and has no declaration.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`:
  `coefficientMap`, `comapLowerStarIso`, `comapOpenImmersionLowerShriekIso`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `CondensedRing.lowerStar`, `upperStar`, `upperStarLowerStarAdjunction`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`:
  `CondensedRing.openImmersionLowerShriek` with its genuine scalar action.
- `Sheaf.Paper.CoefficientHeartStratificationDefs`: `IsLisseCoefficientModule`.
- `Sheaf.Paper.FormalClosedSupport`: `formalClosedSupportAssertions`; its public
  `FormalClosedSupportAdjunction` dependency supplies `formalClosedSupport`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom` and its Tensor
  dependency supply `derivedTensor` and the closed derived structures.
- `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses`:
  the H0/RΓ convention, realized by the existing internal-module `stratumRGamma`.
- `Sheaf.SixFunctors.ProEtale.DerivedCompletion`: `IsDerivedComplete`,
  `AdicCompletion.Modules`, `finiteRing`, `quotient`, `transition`, `quotient_transition`,
  `restrict`, `derivedReduction`, `integralLevel`, `integralStep` and the derived
  change-of-scalars adjunctions.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `IsDerivedLimitTriangle`, `IsDerivedLimit` with precisely the 1-minus-shift convention.
- `Sheaf.AlgebraicGeometry.ClosedSupportStratumHom`: the three unchanged definitions
  `stratumDual`, `stratumGlobalRHom`, and `stratumRGamma`, now owned by the definition
  node `def-sfb-stratum-hom-sections-dual`. The theorem `closedSupport_stratum_globalHom`
  is a proof input only; its node remains in proof_deps, not stmt_deps.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence` reconciles the
  internal and sectionwise presentations of Hom from the regular coefficient module.
- All recorded modules for the stated proof dependencies are also imported. The
  Noetherian compact-subset and right-adjoint limit lemmas without module records
  introduce no extra statement data. There is no import cycle.

Edge cases checked before writing and during rereading: rank-zero L or M; the empty
source or target stratum; empty X; i or h the identity; uS or v the identity; empty
closed support; locally varying finite ranks; arbitrary positive finite levels
(including exponent one); all negative cohomological degrees. No uniform rank,
nonempty stratum, boundedness, or positive-q hypothesis was introduced. Completeness
is canonical, and the products are existential conclusions, not vacuous hypotheses.

Searches for an existing exact statement:

- msearch.py leanfinder: "Supported integral lisse lattice derived Hom is derived
  inverse limit of quotient reductions". Eight hits, including BDeRhamPlus,
  localCohomology.diagram and Condensed.profiniteSolid; no supported lattice Hom tower.
- msearch.py loogle: "IsDerivedLimit, DerivedCategory". Zero hits; IsDerivedLimit
  is a project declaration, not a Mathlib identifier indexed by Loogle.
- msearch.py grep: "lattice.*[Tt]ower|supported.*[Hh]om|IsDerivedLimit" in
  Mathlib/Algebra/Homology. Five support-of-complex embedding hits, no match.
- msearch.py leansearch: "A supported lisse integral sheaf is derived complete and
  global derived Hom is the derived inverse limit of its quotient reductions".
  Eight hits on limits of condensed modules, sheaves of modules, schemes and profinite
  spaces; none states the derived supported-lattice comparison.
- rg on lean/WeilConjectures and lean/Sheaf for lattice towers and supported Hom:
  related integral-lisse reduction and other supported-Hom interfaces were found,
  but none gives this statement. The blueprint id and proposed namespace/theorem
  name have no matches in either source root. In particular the existing stratum
  Hom theorem has no reduction/completeness/Roos conclusion, so it is used rather
  than recorded as an exact existing match.

Validation: the final module compiles through scompile.py under both its sandbox
and actual module names; no errors or warnings other than the expected postponed
proof warning. No local or global build was run. The live repository was read only.
There is no statement correction, dependency-module repair, or STATEMENT-DISPUTED flag.
The returned-delivery repair adds one definition node with an existing:true record;
it adds no Lean definition and changes no existing signature or body.

## Second reading by Q10

The dispatcher forbids starting other agents. This section records a second pass by
this worker, not an independent reviewer; the maintainer's independent review remains
necessary. I reread the DAG statement, every helper, Assertions, and the theorem.
The first pass left the equivalence of the integral presentation and Res_n N-bar_n
implicit: I added the actual `finiteDerivedExtension` and `levelRestrictionIso`
constructions to make it reviewable. The shift comparisons in the two transported
Roos triangles are canonical, not existential unrelated maps. The product projection
normalizations, reduction-unit equation, transition equation, both derived-Hom
comparisons, and both all-integer cohomology clauses are all present explicitly.
No additional mathematical hypothesis or restricted edge case was found.


## New nodes

`def-sfb-stratum-hom-sections-dual` owns exactly the existing definitions
`AlgebraicGeometry.ProEtale.CondensedRing.stratumGlobalRHom`, `stratumRGamma`, and
`stratumDual` in `Sheaf.AlgebraicGeometry.ClosedSupportStratumHom`, lines 49–65.
Its existing:true record leaves that landed module and its declarations untouched.
The definition node cites `def-pur-sheaf-hom`, `def-pur-hom-complex`, and
`def-pur-ringed-site-zeroth-hypercohomology`, as requested by the return, together
with the actual coefficient, category, size and section-action-equivalence definitions.
Its source is the current blueprint's uniform-constructible-Ext proof, Integral targets,
the displayed RHom/RΓ equality and preceding definition of F. The stratum-Hom blueprint
statement also explicitly defines the dual as sheaf Hom into the coefficient module.

The node introduces arbitrary commutative condensed Λ, arbitrary X and arbitrary M,L.
It does not assume admissibility or finite local freeness. It defines global RHom from
M[0] by the right derived additive Hom functor; it defines RΓ by M=regular module; and
it defines the internal dual by `(ihom L).obj (𝟙_ _)`. Thus no theorem is used to
construct its data. On a K-injective representative I, the source M[0] collapses the
Hom-complex product to Hom(M,I^q) in degree q, with postcomposition differential.
This is why the recorded `preadditiveCoyoneda.rightDerivedFunctor` is global RHom,
including for negative q and zero M.

Reconciliation of RΓ (H4): put J=`Scheme.ProEt.topology X`, B=`condensedRingObj Λ X`,
and take the concrete equivalence F=`sectionModuleEquivalence J B`. Its section ring
is `sectionRingSheaf J B`; this is the ring argument of
`ringedSiteZerothHypercohomologyOfUniverses`. F preserves underlying sections and
restrictions, and changes the tensor action to `r • m = act(r ⊗ m)`. For the regular
module the action is multiplication, so F(regular B) is canonically the unit sheaf
via the identity on section elements. Full faithfulness then identifies, naturally
in M, Hom_internal(regular B,M) with Hom_sectionwise(unit,F(M)); evaluation at 1
identifies both with the compatible families of global sections. These identifications
commute with postcomposition, hence with every differential on a complex. The exact
equivalence preserves K-injective complexes (test acyclic complexes through its exact
inverse), so applying this identification termwise to a K-injective representative
identifies the full right derived functors. Composing with zeroth homology gives
exactly the recorded `ringedSiteZerothHypercohomologyOfUniverses`; it does not identify
a D(Ab)-valued functor with an Ab-valued H0 functor. At the small pro-etale site the
site-object universe is u+1, its arrow universe is u, and sections live in u+1,
so max(c,v,r)=u+1 and this comparison changes no universe or coefficient object.
No independent RΓ is defined, and no comparison assumption is added to the item.

Searches run during this repair (all msearch calls used Q10 and this item):

- LeanSearch, “Global derived Hom of module sheaves is the right derived functor of
  Hom and derived global sections is Hom from the regular module”: eight hits,
  including `Functor.rightDerived`, `Scheme.Modules.Hom`, `Sheaf.Γ`, `sheafHom`,
  and `rightDerivedToHomotopyCategory`; none is the combined unbounded internal-module
  interface. The complete hit list is retained in the new node's mathlib_searches.
- LeanFinder, “Internal Hom dual of a sheaf of modules and global derived sections
  as derived Hom from the regular coefficient module”: eight hits, including
  `SheafOfModules.unitHomEquiv`, `LightCondensed.ihomPoints`, `Sheaf.ΓHomEquiv`
  and sheafification Hom equivalences; no combined interface.
- msearch grep, `preadditiveCoyoneda|rightDerivedFunctor|ihom` in Algebra/Homology:
  fourteen hits on bounded-below derived functors and Ext exact sequences, no exact
  definition. Direct rg in WeilConjectures and Sheaf finds the exact existing three
  definitions only in `ClosedSupportStratumHom`, which are reused unchanged.
- Direct DAG name/concept searches and `blueprint_refs.py search` for “global derived
  Hom”, “RΓ”, and “internal dual” found comparison lemmas and unrelated definitions,
  with no independent definition node for these three notions. Existing
  `def-pc-global-derived-rhom` and `def-weil-pbc-adic-global-derived-hom` use other
  coefficient/module categories. `blueprint_refs.py ancestor` gives
  `det-uniform-constructible-ext-integral`, recorded as the new node's ancestor.

## Repair of return L at d5b286bb7b51

H2: removed `det-lem-formal-closed-support-stratum-hom` from stmt_deps and added
`def-sfb-stratum-hom-sections-dual` in sec-six-functors-basics. The former remains
unchanged in proof_deps and proof step 10, where its comparison theorem is needed.
The new node owns only the already-landed definitions; no definition is moved out
of or duplicated from `ClosedSupportStratumHom`.

H4: the new node explicitly cites the ringed-site hypercohomology convention, and
its statement, lean.note and the detailed reconciliation above explain the exact
ordinary Hom, K-injective, section-action, regular/unit and H0 identifications.
The item's formulas still use the same three declarations, with no altered
hypothesis or conclusion. The module-level documentation now names their definition
node and distinguishes full derived sections from its zeroth hypercohomology.

Saved-packet audit: the first prescribed dry run passed (commit 5e81111fd91), but
that did not resolve the independent mathematical return, so the packet was repaired.
A field comparison with the current shared main source found only lean and stmt_deps
changed; the returned theorem-node addition was the only saved-only stmt_dep.
No direct git command or shared-source mutation was used.

## Second reading by Q10 (repair)

I reread the retained item and all clauses of Assertions against the return. The
repair changes no signature, binder, definition body, projection normalization,
shift comparison or conclusion. The only graph replacement is the erroneous
statement dependency on a theorem by the owning definition node. The new node is
strictly definitional, has no proof or proof dependencies, and has real existing
data in all three declarations. Reading the H0 declaration and its universes showed
that it is the same Hom-from-unit-derived-sections construction after H0 in the
sectionwise presentation; the explanation now accounts for that presentation and
for u+1 sections explicitly. Rank zero, empty strata and all integer q remain
allowed. No independent agent was started, as the dispatcher forbids delegation.

Repair validation: scompile.py compiled both sandbox and actual module names cleanly
(13.4 s and 16.0 s); no errors or unexpected warnings. The repaired dry run passed
as d23d756a1a5, checking both the unchanged existing-definition interface and the
consumer module. Final self-check confirms the new node's bracket citations equal
its stmt_deps, the item's recorded signature is verbatim, all Lean lines are at
most 100 characters, the only sorry is the main theorem, and the item's base-field
delta is exactly lean plus addition of the new definition node to stmt_deps.
