## Worker report

The delivered module is `Sheaf.SixFunctors.EtaleStalkConstantComplexExactness`.
Its ten declarations jointly state the node. The four construction interfaces are
transparent specializations/compositions of existing declarations; the six theorem
proofs are `sorry`. There are no new nodes, dependency repairs, or statement corrections.
The node's original statement and six-step proof are unchanged. Its stmt_deps gains
exactly two already landed dependencies used by the canonical constructions:
`def-sf-site-constant-module-functor` and `def-sfb-constant-ring-module-restriction`.

Hypothesis and clause correspondence:

- Scheme T: `(T : Scheme.{u})`, with the original Mathlib scheme and morphism category.
- Arbitrary commutative ring A: `(A : Type (u + 1)) [CommRing A]`. This is the coefficient
  size convention of the recorded constant-sheaf dependency on the site whose objects
  have universe u+1 and arrows have universe u. It imposes no algebraic finiteness or
  nonzero-ring condition. Smaller coefficient types can inhabit this universe; any
  larger coefficient and scheme sizes can be put in a common ambient universe.
- Geometric point: `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]` and
  `(t : Spec (.of Ω) ⟶ T)`. No extra hypothesis on its image or residue extension.
- Small étale site: `T.smallEtaleTopology` on `T.Etale`, without extra site assumptions.
- Constant ring sheaf: `etaleConstantComplexRing T A` is literally the existing
  `constantSheaf ... RingCat` evaluated at `RingCat.of A`.
- Sheaves of A_T-modules: `etaleConstantComplexModules T A` is literally the recorded
  `ringedSiteModules.{u + 1}` at that ring sheaf, hence Mathlib `SheafOfModules` with
  its existing abelian instance. No alternative abelian or derived structure is chosen.
- c(M): `etaleConstantComplexFunctor T A` is literally
  `siteConstantModuleFunctorGeneral T.smallEtaleTopology A`: constant presheaf of
  modules with identity restrictions, followed by genuine module sheafification
  along the constant ring sheafification unit. Its underlying abelian sheaf is
  the abelian constant sheaf, as provided by the recorded module-sheafification API.
- S(F) with induced A-action: `etaleConstantModuleStalkFunctor A t` is
  `constantRingModuleRestriction ... A ⋙ (pointSmallEtale t).sheafFiber`.
  The first functor restricts each section's action along the actual A → A_T(U)
  sheafification unit and retains the same sections and underlying additive maps.
  The second takes their pointed-neighbourhood colimit in ModuleCat A. Thus a acts
  on a germ by the germ of its constant section times the original section. The
  object is definitionally `pointedEtaleStalk` of the restricted sheaf; the final
  theorem explicitly uses the recorded `pointedEtaleGerm`, which typechecks against it.
- Both functors additive: `etaleConstantComplexFunctor_additive` and
  `etaleConstantModuleStalkFunctor_additive`. These proofs supply global additivity
  instances for the termwise functors; there are no file-local instances.
- Both functors exact: the four conjuncts of `etale_stalk_constant_exact` assert
  `PreservesFiniteLimits` and `PreservesFiniteColimits` for c and S. In these abelian
  categories this is precisely additive exactness, with its finite-biproduct
  consequences. The proof docstring spells out the short-exact-sequence argument.
- Unbounded cochain complexes and termwise application: `CochainComplex ... ℤ` and
  `Functor.mapHomologicalComplex (.up ℤ)`, exactly as the recorded complex dependency.
  No bounds, resolutions, or localizations appear in the statement.
- H^n(SC) ≅ S(H^n(C)) and H^n(cE) ≅ c(H^n(E)): the two conjuncts of
  `etale_stalk_constant_cohomology`, for every `(n : ℤ)`, are `Nonempty` natural
  isomorphisms of the indicated composites with `HomologicalComplex.homologyFunctor`.
  Their naturality is part of NatIso, not merely a family of object isomorphisms.
  The first is in ModuleCat A (A-linear), the second in Mod(A_T) (A_T-linear).
- Acyclicity preservation: the first two conjuncts of `etale_stalk_constant_preserves`
  quantify over all C and E and send `C.Acyclic` / `E.Acyclic` to the same predicate
  on their termwise images.
- Quasi-isomorphism preservation: the last two conjuncts quantify over every chain
  map f and send Mathlib `QuasiIso f` to `QuasiIso` of the termwise image.
- Natural chain isomorphism η_E: the first conjunct of
  `etale_stalk_constant_complex_retraction` is `∃ η : 𝟭 ... ≅ c_* ⋙ S_*, ...`.
  Hence it is a chain isomorphism natural in the entire complex E, in the required
  direction E → S(cE), with an actual inverse and differential compatibility.
- Prescribed components: the equality for every E, n and e identifies
  `((η.hom.app E).f n) e` with the abelian sheafification unit at
  `op (Etale.mk (𝟙 T))`, followed by `pointedEtaleGerm` at lift
  `Over.homMk t (Category.comp_id t)`. This is exactly the germ at (T,t) of e's
  global constant section, and fixes the chain isomorphism, including its sign.
- S(A_T) ≅ A with ordinary scalar action: the second conjunct is a module isomorphism
  `ModuleCat.of A A ≅ S.obj (SheafOfModules.unit A_T)`, with each a sent to the germ
  of the ring sheafification unit. Its source action is multiplication in A;
  its A-linearity is part of being an isomorphism in ModuleCat A. Thus the stated
  normalization identifies the induced action with ordinary multiplication.
  The orientation is immaterial to the displayed isomorphism in the node.
- Arbitrary unbounded complexes and arbitrary A: none of the theorem binders adds
  Finite, Module.Finite, Noetherian, boundedness, nontriviality, or a geometric
  regularity assumption.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Mathlib.FieldTheory.IsAlgClosed.Basic and Mathlib.AlgebraicGeometry.ResidueField:
  `IsAlgClosed`, `Scheme.SpecToEquivOfField` (geometric-point convention).
- Mathlib.AlgebraicGeometry.Sites.Etale and EtalePoint:
  `Scheme.smallEtaleTopology`, `Scheme.Etale`, `Scheme.pointSmallEtale`.
- Sheaf.AlgebraicGeometry.PointedEtaleStalk:
  `pointedEtaleStalkDiagram`, `pointedEtaleStalk`, `pointedEtaleGerm`.
- Sheaf.CategoryTheory.RingedSiteModules: `CategoryTheory.ringedSiteModules`;
  Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian supplies its original abelian instance.
- Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral:
  `siteConstantModulePresheafGeneral`, `siteConstantModuleFunctorGeneral`.
- Sheaf.CategoryTheory.ConstantRingModuleSheaves:
  `constantRingModuleRestrictionPresheaf`, `constantRingModuleRestriction`, recorded by
  `def-sfb-constant-ring-module-restriction`. The restriction functor's full signature and
  definition retain the canonical constant-ring action rather than choosing any functor.
- Mathlib.Algebra.Homology.Additive:
  `Functor.mapHomologicalComplex`; Mathlib.Algebra.Homology.DerivedCategory.Basic:
  `DerivedCategory` / `HasDerivedCategory` read for the dependency, though this node
  only needs the underlying unbounded complexes, homology and quasi-isomorphisms.
- Proof-dependency imports: WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
  (`Scheme.constantSheaf_geometricStalk_isIso`),
  WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
  (`CategoryTheory.moduleSheaves_colimits_forgetful`),
  Mathlib's module-presheaf sheafification API and ordinary sheafification exactness
  (already available through the public construction dependencies), and
  `Functor.homologyFunctorIso` from ShortComplex.PreservesHomology.
  Point.Basic/Skyscraper provides exact geometric abelian stalks.
  No proof dependency is omitted because of a cycle.

Sources opened: sites-modules.tex, `lemma-sheafification-exact` (03EI) and
`lemma-stalk-exact-modules` (04EQ), including the preceding definition of the stalk
module action; etale-cohomology.tex, `lemma-stalk-exact` (03PT), especially clause (2).
The module docstrings carry the proof in the node's order: exact sheafification,
constant-germ linearity and naturality, exact stalks, cohomology comparisons,
acyclicity and quasi-isomorphisms, and the degreewise chain inverse.

Edge cases checked before writing: A=0, zero modules and complexes, negative and
zero degrees, unbounded complexes with nonzero differentials, and no Noetherianity
or torsion hypothesis. The empty scheme admits no geometric point, so the statements
with t have no instance there; the constant functor's additivity still applies.
For T=Spec of an algebraically closed field the constant-germ formula specializes
correctly. No separate finite-module constant-sheaf theorem is used. For an unbounded
acyclic example, E^n=A² with d(a,b)=(b,0) is covered degreewise in all n.

Searches actually run on 2026-10-21, using the prescribed msearch.py wrapper:

- LeanFinder: `The geometric stalk functor on sheaves of modules over a constant ring
  is exact and retracts the constant module sheaf functor on unbounded complexes`.
  Eight hits, including CompHausLike.LocallyConstantModule.functor,
  CondensedMod.LocallyConstant.functor, and ModuleCat.Tilde.toStalk. These address
  condensed or Zariski constructions, not this normalized étale complex theorem.
- Loogle: `"sheafFiber", "constantSheaf"`. OK, zero hits.
- Mathlib grep: `sheafFiber.*[Mm]odule|[Mm]odule.*sheafFiber|constantSheaf.*[Ee]xact`.
  OK, zero hits.
- LeanSearch: `The constant sheaf functor on modules and geometric stalk functor are
  exact and commute with cohomology of unbounded complexes`. Eight hits, including
  CategoryTheory.constantSheaf, constantCommuteCompose, Sheaf.isConstant_of_forget,
  and condensed locally-constant functors. These provide ingredients, not the full node.
- Source/project rg: `constant.*[Mm]odule|[Mm]odule.*[Ss]talk|[Ss]talk.*[Mm]odule|constantRingSheaf`
  in the named Sheaf and WeilConjectures topic directories, followed by narrower
  `siteConstantModuleFunctorGeneral|finiteCoefficientModuleStalkFunctor|constantRing_moduleSheaf_equivalence`
  and `constant.*[Ee]quiv|[Ee]quiv.*constant`. Found and read the general constant
  module functor, scalar restriction, the pro-étale stalk functor, the finite-ring
  equivalence, and general ringed-site tensor interfaces. Reused the two general
  landed constructions; the pro-étale/finite-ring interfaces are different objects.
- `rg -n 'lem-sfb-etale-stalk-constant-complex-exactness|constant.*[Mm]odule.*[Ss]talk|[Ss]talk.*constant.*[Mm]odule'`
  in both project roots found related tensor and Zariski/pro-étale results but no
  declaration for this item. A further `etaleConstantModuleFunctor` search found the
  known equivalence from fixed-ring sheaves to ringed modules, which is not the
  constant-module functor from ordinary modules used here.

No STATEMENT-DISPUTED finding and no node fault. The four construction declarations
are public transparent aliases/composition; there is no data chosen from an unproved
existence statement. Every postponed theorem is a clause of this node and carries
its source, blueprint id, and complete proof docstring.

Validation: prescribed scompile.py compiled the sandbox and the final library-name
module cleanly (14.9 s and 12.9 s), with no diagnostics. The initial compile exposed
only the global namespace of Mathlib QuasiIso and an acyclicity projection syntax
issue; both were corrected before the clean compile. No lake/global build was run.

## Second reading by NE

Author self-reading under the direct-dispatch instruction prohibiting other agents:
reopened the node and the complete file and compared all clauses as listed above.
In particular, the coefficients are genuine A_T-modules, not merely a replacement
category of module-valued sheaves; scalar restriction precedes the module colimit;
all homology comparisons are natural isomorphisms; both acyclicity and both
quasi-isomorphism assertions are present; and η goes from E to S(cE), with every
integer-degree component fixed by the original constant-section unit and the
recorded germ at (T,t). The regular-module comparison explicitly uses
SheafOfModules.unit, not a free rank-one object with an unspecified identification.
The final statements contain no local notation, local instances, let binders,
arbitrary comparison hypotheses, bounds, or finiteness assumptions. No mathematical
mismatch was found. The proof docstrings collectively cover every step of the
node's six-step proof, and only the theorem proof fields contain sorry.

Repair of returned head `3da47abf31bc` (H2/H12, 2026-10-21): replaced the added
statement dependency `lem-cbc-constant-ring-module-sheaves` with the existing definition
node `def-sfb-constant-ring-module-restriction`. Read that node's existing:true ownership
record and the definitions in `Sheaf.CategoryTheory.ConstantRingModuleSheaves`: the
section action is restricted along the constant-ring sheafification unit, with the
same section maps. The module uses this plain definition, never an equivalence chosen
from `constant_ring_module_sheaves`. Its site specialization has object universe u+1,
arrow universe u, and coefficient universe max (u+1) u = u+1, matching the definition
node. No Lean source, mathematical statement, proof field, or other node field changed
in this repair. The saved packet first passed the required dry run; the corrected
packet was revalidated before delivery: scompile.py passed for both the sandbox
and final library-name module (14.9 s and 12.9 s), with no diagnostics. The repair
self-check verified the exact two added definition dependencies, verbatim theorem
signature, six sorry theorem proofs, and no changes to other original node fields.
