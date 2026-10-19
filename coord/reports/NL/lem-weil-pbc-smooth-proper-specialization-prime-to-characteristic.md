## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothProperPrimeSpecialization` states
`AlgebraicGeometry.Etale.isIso_strictLocalSpecialization_smooth_proper_prime`.
Its only postponed proof is the main theorem, with the five-step DAG proof in
its docstring. The helper `strictLocalSpecialization` has real data: uniquely
characterized restriction to the strict localization, evaluation at its terminal
etale neighbourhood, taking the germ at t, and the canonical inverse-image stalk
comparison. This introduces the very specialization map specified in the item,
not an arbitrary homomorphism or an abstract isomorphism. No additional theorem
or independent definition node is needed for this helper.

Clause-by-clause correspondence:

- Schemes X and S and their morphism are `{X S : Scheme.{u}} (f : X ⟶ S)`.
- Smoothness and properness are `[Smooth f] [IsProper f]`.
- The prime is `(ell : ℕ) [Fact ell.Prime]`.
- Invertibility on S is `hunit : ∀ x : S, IsUnit (ell : S.presheaf.stalk x)`;
  these are exactly the local rings, not an assumption only on global sections.
- F is `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))`.
  The standard universe lift is canonically ring-isomorphic to the prime field;
  it changes neither coefficient modules nor their linear morphisms. It places
  the coefficient ring in the same u+1 universe as the module category, as
  required by the existing Grothendieck-category instance. This is the existing
  coefficientwise ModuleCat sheaf encoding used by the constructibility API,
  not a newly constructed module-sheaf category.
- Local constancy is `[Scheme.IsLocallyConstantSheaf F]`, which supplies exactly
  a jointly surjective etale trivializing cover with constant localized sheaves.
- Every nonnegative degree is `(q : ℕ)`; its cohomological index is `(q : ℤ)`.
- The geometric point s is over an arbitrary algebraically closed field Ω;
  t is over a separately quantified algebraically closed Ω' and maps to
  `Scheme.strictHenselizationScheme s`. There is no algebraicity assumption
  on either point's field over the residue field.
- The underlying abelian sheaf is `(sheafCompose ... (forget₂ ...)).obj F`.
  This is the abelian interpretation of higher direct images expressly allowed
  in the node ("regarded also as an abelian sheaf"). The conclusion concerns
  its canonical abelian specialization, not a newly chosen module/abelian
  comparison. The proof docstring also describes the module interpretation.
- R^q is `DerivedCategory.Plus.homologyFunctor _ (q : ℤ)` after
  `rightDerivedLowerStarPlus AddCommGrpCat f` on `Plus.singleFunctor _ 0`.
- Source and target of the helper are `(pointSmallEtale s).sheafFiber.obj G`
  and the stalk at `t ≫ strictHenselizationStructuralMap s`, respectively.
- The conclusion `IsIso (strictLocalSpecialization s t ...)` asserts
  invertibility of that specific pointed-neighbourhood restriction map.
- Neither relative dimension nor finite stalks appear among the hypotheses.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`, `Scheme.Etale`.
- `WeilConjectures.ConstructibleSheaf.Defs`: `Scheme.IsLocallyConstantSheaf`
  and its `LocallyConstantDatum`; this is the recorded declaration, present in
  the pinned slopmaster2 source despite its older master branch metadata.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`
  was read. The item uses the equivalent existing coefficientwise ModuleCat
  encoding required by `IsLocallyConstantSheaf`, consistent with the stage rule
  for constructible module sheaves; it creates no duplicate category.
- `Sheaf.AlgebraicGeometry.StrictHenselization`: `Scheme.strictHenselizationScheme`
  is the spectrum of the small pointed-affine coordinate-ring colimit.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.lowerStar`;
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`:
  `Etale.rightDerivedLowerStarPlus`. The latter is the actual current module
  defining the recorded derived declaration.
- `Mathlib.CategoryTheory.Sites.Point.Basic`: `Point.sheafFiber`,
  `Point.toPresheafFiber`; `Mathlib.AlgebraicGeometry.Sites.EtalePoint`:
  `Scheme.pointSmallEtale`.
- Added landed statement dependency `def-weil-pbc-strict-henselization-restriction`:
  `Etale.existsUnique_strictHenselizationStalkRestriction` in
  `Sheaf.AlgebraicGeometry.StrictHenselizationRestriction`, used by choice of
  the UNIQUE map characterized on every representative pointed neighbourhood.
- Added landed statement dependency `lem-weil-pbc-inverse-image-stalk-germ`:
  `AlgebraicGeometry.inverseImage_stalk_germ` in
  `Sheaf.Paper.InverseImageStalkGerm`, whose explicit canonical comparison
  `Etale.upperStarCompSheafFiberIso` is used in the helper. Its germ compatibility
  identifies the composite helper with the restriction described in the node.
- The recorded proof dependency module
  `Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison` is imported
  non-publicly. The three other proof-only theorem nodes have no Lean record,
  so there is no module to import yet; none is needed to TYPE this statement.

Edge cases: q=0 is included; empty X is permitted, and empty S simply has no
geometric point to test. Infinite dimensional stalks and unbounded relative
dimensions are not excluded. The prime hypothesis rules out ell=0 and ell=1;
characteristic zero is allowed. In residue characteristic ell, hunit fails at
that point, as it must. The point t may be the distinguished closed geometric
point or lie above a generization, with arbitrary algebraically closed field
extension. Universes of the two point fields are independent instances in the
common scheme universe; larger fields and schemes can be placed in a common
universe. No equality of distinct site universes is introduced.

Source checked: `literature/stacks-project/etale-cohomology.tex`,
`lemma-sp-isom-proper-loc-cst-torsion` (Tag 0GKD), statement and proof. It has
smooth/proper, locally constant and prime-to-residue-characteristic torsion
hypotheses, no finiteness or relative-dimension hypothesis. The node's prime
module formulation is its indicated special case and degree-q consequence.
No statement correction or disputed statement.

Searches:

- msearch leanfinder: "smooth proper morphism locally constant prime to
  characteristic etale sheaf specialization isomorphism": eight hits, concerning
  etale loci, ring maps and specializing scheme maps; none states this theorem.
- msearch loogle: `"specialization", "Sheaf"`: zero hits.
- msearch grep: `specialization.*(sheaf|cohomology)|locallyAcyclic`: zero hits.
- rg of the upstream WeilConjectures tree for specialization/specialisation:
  topology and compactification results, no etale sheaf specialization theorem.
  Search for the exact node id in the source tree: no match.
- rg of project `lean/Sheaf` and scan of DAG titles/statements: the proper
  locally acyclic specialization and specialization/cospecialization nodes are
  unstated theorem nodes, not definitions of a missing independent object.
  The landed strict-local restriction and inverse-image stalk maps supply the
  full canonical specialization construction without waiting on these proofs.
- Full-name searches of Mathlib, upstream, project and upstream-name inventory
  found no existing `strictLocalSpecialization` or
  `isIso_strictLocalSpecialization_smooth_proper_prime`.

Validation: server scompile succeeded cleanly (3.1 seconds, nice 19, two threads,
60-second limit). No local compile or library build was run. Second reading is
left to the separately dispatched reader, as required by the brief.

## Second reading by NL

Independent second reader; the author was another dispatched worker. Read the
item JSON and both declarations in SmoothProperPrimeSpecialization.lean against
Stacks etale-cohomology.tex, lemma-sp-isom-proper-loc-cst-torsion (0GKD), its
proof, lemma-sp-isom-proper-torsion-loc-ac (0GJW), and the preceding specialization
construction (including remark-another-sp). There are no ambient Noetherian,
finite-stalk, or relative-dimension hypotheses in this source.

Object/hypothesis/conclusion checklist (the node's statement, in order):

1. Arbitrary schemes X and S, and their morphism f: `{X S : Scheme.{u}}`
   and `(f : X ⟶ S)`. PASS. Read the Smooth and Proper Mathlib definitions:
   `[Smooth f] [IsProper f]` are the recorded smooth/proper notions. The latter
   includes universal closedness and therefore quasi-compactness; no extra
   finite-type or separated assumption is being imposed.
2. Prime ell: `(ell : ℕ) [Fact ell.Prime]`. PASS. ZMod ell is the prime field.
3. Ell invertible on S: `hunit : ∀ x : S, IsUnit (ell : S.presheaf.stalk x)`.
   PASS: these are all local rings, not only global sections or selected points.
4. A sheaf F of F_ell-modules on X_et: `F : Sheaf X.smallEtaleTopology
   (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ell)))`. PASS. Read the small etale
   site definition and the RingedSiteModules dependency. The established
   coefficientwise ModuleCat encoding gives exactly constant-coefficient module
   sheaves, with linear restriction maps. ULift transports the coefficient ring
   along its canonical ring equivalence and puts modules in the required
   Grothendieck universe; it adds no finiteness or algebraic restriction.
5. Local constancy: `[Scheme.IsLocallyConstantSheaf F]`. PASS. Opened upstream
   ConstructibleSheaf.Defs: LocallyConstantDatum consists of a jointly surjective
   etale cover with constant restrictions on the localized sites, and the class
   asserts existence of that datum. It does not assert constructibility or
   finite generation.
6. Regard F also as an abelian sheaf: `(sheafCompose ... (forget₂ ...
   AddCommGrpCat.{u + 1})).obj F`. PASS. The node explicitly allows this
   interpretation. No arbitrary underlying sheaf is substituted for F.
7. Every q >= 0: `(q : ℕ)`, used as `(q : ℤ)` in homology. PASS.
   `Plus.singleFunctor _ 0`, `rightDerivedLowerStarPlus ... f`, and
   `Plus.homologyFunctor _ (q : ℤ)` implement F[0], Rf_*, and R^qf_* in that
   order. Read lowerStar in UpperLowerStar.Defs and its bounded below derived
   functor in Derived.UpperLowerStarCoherence: they are the recorded direct
   images, not an alternative cohomology construction.
8. Every geometric s: `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`
   and `(s : Spec (.of Ω) ⟶ S)`. PASS, with no algebraicity requirement.
9. Every geometric t of S_(s): independently quantified Ω', Field, IsAlgClosed,
   and `(t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s)`. PASS.
   Read StrictHenselization: it is Spec of the coordinate-ring colimit on a
   small representative model of all affine pointed etale neighbourhoods.
10. Source and target stalks: helper source `(pointSmallEtale s).sheafFiber.obj G`
    and target `(pointSmallEtale (t ≫ strictHenselizationStructuralMap s))
    .sheafFiber.obj G`. PASS. Read Point.sheafFiber and pointSmallEtale: the
    colimit is over opposite pointed-neighbourhoods and the target is the image
    point on S, as required by the displayed node formula.
11. The specified specialization arrow: `strictLocalSpecialization s t G`.
    PASS. Opened StrictHenselizationRestriction: `IsStrictHenselizationStalkRestriction`
    prescribes every representative germ component via the inverse-image unit
    and the strict-local limit leg. Its existence theorem asserts UNIQUE
    existence, so `Classical.choose` here chooses determined data, not an
    arbitrary map. The remaining factors evaluate global sections at the
    identity terminal etale object, take the germ at t, and apply
    `upperStarCompSheafFiberIso`. Read that canonical isomorphism in upstream
    Stalk.lean and inverseImage_stalk_germ in the project; their germ formulas
    identify this composite with restriction through S_(s). This is precisely
    the map whose invertibility is asserted, with no abstract-isomorphism
    replacement or downstream specialization theorem needed to define it.
12. Isomorphism for all q,s,t: `IsIso (strictLocalSpecialization s t (...))`.
    PASS. Quantifiers follow the node order, and the conclusion covers its sole
    clause. No finite-stalk or relative-dimension binder occurs.

Edge cases: zero module/sheaf, empty X, q=0, and identity morphisms are allowed.
Empty S has no geometric s and hence is vacuous, as in the source. There is no
index family in this statement. Ell=0,1 are excluded exactly by primality;
residue characteristic ell is excluded exactly by hunit, and characteristic zero
is included. Closed-point t, generizations, and nonalgebraic field extensions
are included. The arbitrary common universe u can contain schemes and both
point fields, with coefficient objects in u+1; no site object/morphism universe
equality or additional universe-class hypothesis is imposed.

Independent searches (different wording from the author):

- msearch leanfinder: "Higher direct image stalks of locally constant finite
  characteristic modules along smooth proper maps are invariant under
  generization" returned eight results on topological stalk pushforward,
  spreading out, and module ranks; none states this etale specialization theorem.
- msearch loogle: `"specialization"` returned twelve compiler/topological-order
  declarations, none an etale sheaf specialization map or this theorem.
- msearch grep: `smooth.*proper.*(stalk|speciali)|speciali.*(etale|torsion)`
  returned one unrelated regular-sequence hit.
- Independent rg of project lean/Sheaf, upstream WeilConjectures and Mathlib
  for specialization/specialisation, locallyAcyclic, etale/sheaf combinations,
  and both proposed full declaration names: no existing copy. Topological
  stalkSpecializes and the generic-module stalk map concern different sites.
  The actual strict-local restriction and inverse-image stalk dependencies are
  reused. DAG records for the later local-acyclicity theorems provide proof
  inputs, not a competing construction needed for this signature.

No new definition node or dependency module is in this delivery. The two added
statement dependencies are already landed and were read in full at their
relevant interfaces. No statement_change is present or needed. Checked the
five-step proof docstring against the node: forget scalars and check torsion;
smooth universal local acyclicity; local acyclicity relative to this sheaf;
proper specialization; optional exact module/abelian comparison. The sole
postponed proof is the named main theorem. Helper data is fully constructed;
its embedded `by simp` only proves the over-category commutativity equation.
Module and declaration source/blueprint docstrings and public names comply.
All universe and term variables are explicitly bound. The recorded theorem
signature is unchanged and agrees verbatim with the source signature.

Mismatches found: none. Changes: appended this independent second reading only;
Lean and node records retained. Validation is the server single-file compile
and delivery preflight below, using the mandated scompile path and limits.
