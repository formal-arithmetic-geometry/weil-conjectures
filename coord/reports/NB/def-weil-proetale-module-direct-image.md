## Worker report

Existing declaration: `AlgebraicGeometry.Scheme.proEtaleConstantModuleDirectImage`,
in `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`, lines 233–248 of the group checkout.
Its full definition and docstring were read, together with every recorded dependency
module. No new Lean module, definition, theorem, dependency repair, or statement
correction is needed. The node changes only in `lean`, with `existing: true`.

Source checked: Stacks `sites-modules.tex`, Tag 03D6, label
`definition-pushforward`, clause (1), lines 1145–1171: the underlying abelian sheaf
is direct image and its scalar action is restriction through the structure map.
Also `proetale.tex`, Tag 09A5, label `section-morphism`, lines 4674–4681:
base change along every scheme morphism induces the small-site morphism.
The blueprint `def-weil-derived-direct-image.md` introduces this underived functor
before taking its derived functor; its additional finite-level hypotheses are not
hypotheses of this standalone definition node.

Hypotheses and clauses, matched individually:

- Arbitrary schemes and arbitrary morphism: `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
  There is no weakly-etale, properness, quasi-compactness or separation hypothesis on f.
- Arbitrary commutative ring: `(A : Type u) [CommRing A]`. The coefficient and scheme
  universe convention is exactly the recorded `proEtaleDerivedCategory` convention;
  `ULift.{u+1,u} A` moves the coefficient ring into the section universe.
- Small sites, rings and module categories: `ProEt.topology X`, `ProEt.topology Y`,
  `proEtaleConstantRing X A`, `proEtaleConstantRing Y A`, followed by
  `sheafCompose … (forget₂ CommRingCat RingCat)` and `SheafOfModules.{u+1}`.
  These are definitionally the ring/module presentation inside the recorded derived
  category. `ringedSiteModules` is transparently this same `SheafOfModules`, not
  a competing category. Site objects remain in universe u+1 and Homs in u.
- The specified base-change functor is `proEtaleBaseChange f`, namely
  `MorphismProperty.Over.pullback @WeaklyEtale ⊤ f`. Its continuity, covering
  preservation and finite-limit preservation are recorded in the dependency module.
  It uses V ×_Y X, as the item does.
- The specified constant ring map is `proEtaleCoefficientDirectImageMap f A`.
  Its definition specializes `proEtaleConstantDirectImageMap`; the latter uses the
  sheafification adjunction on the whiskered `toSheafify` map of constant presheaves.
  Thus it extends the specified constant-section map, rather than taking arbitrary
  ring-map data. Whiskering with `forget₂ CommRingCat RingCat` supplies the same rho
  after forgetting commutativity.
- Sections `(f_* F)(V) = F(u_f V)`: the existing definition is exactly
  `SheafOfModules.pushforward` with this base change and rho. Its object field is
  `PresheafOfModules.pushforward rho.hom`, which is `pushforward₀ … ⋙ restrictScalars`.
  `pushforward₀Obj` evaluates the original module at `F.op.obj V`.
- Restrictions are the original module restrictions at the base-changed arrow;
  `PresheafOfModules.pushforward_obj_map_apply` states this pointwise.
- The underlying abelian presheaf is precomposition: `pushforward₀CompToPresheaf`
  and `pushforwardCompToPresheaf` are identity isomorphisms, and the sheaf field in
  `SheafOfModules.pushforward` is supplied by the continuous sheaf direct image.
- Scalar action `(a,s) ↦ rho_V(a) s`: `PresheafOfModules.restrictScalarsObj` uses
  `ModuleCat.restrictScalars (rho.app V).hom`; hence the action is precisely the
  required one. Its restriction-map semilinearity is obtained from naturality of
  rho and the original module's semilinearity, as the node specifies.
- Morphisms `(f_* phi)_V = phi_(u_f V)` are given by `pushforward₀.map` followed
  by restriction of scalars; `pushforward_map_app_apply` states their exact values.
  `ModuleCat.restrictScalars.map` retains the original function and its linearity
  along rho. No extra choice of linear map occurs.
- Identities and composition are the componentwise functor fields of these existing
  functors. Addition of maps is likewise componentwise: the new component is exactly
  the old component, with the same underlying additive groups. This verifies the
  node's additivity clause directly from the construction; the existing declaration
  returns a functor, rather than bundling a separate `Functor.Additive` witness.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` (line 42) and
  `Scheme.Hom` (line 74), their complete signatures and docstrings.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory` (constant ring/module presentation).
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: the full module, particularly
  `proEtaleBaseChange`, `proEtaleBaseChange_isContinuous`,
  `proEtaleBaseChange_preservesFiniteLimits`, `proEtaleBaseChangeCoverPreserving`,
  `proEtaleSheafDirectImage`, `proEtaleConstantDirectImageMap`,
  `proEtaleConstantRing`, `proEtaleCoefficientDirectImageMap`, and the existing
  `proEtaleConstantModuleDirectImage` itself.
- Mathlib `Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous` lines 31–51;
  `Presheaf.Pushforward` lines 30–131; `Presheaf.ChangeOfRings` lines 25–72.
  Their object and morphism definitions establish the sectionwise comparison above.
- Read `coord/pefw-upstream-framework.md` and the exact group-clone
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`
  module introduction, which documents the arbitrary-morphism and size conventions.

Edge cases checked against the definitions: zero ring is allowed (`CommRing` has no
nontriviality premise); the zero module stays zero sectionwise; empty schemes and
empty covering families require no additional data and are handled by the existing
sheaf condition/continuity; identity and composite scheme maps use the same chosen
base-change fibre products (no unjustified literal equality with unchosen products).
No bound on objects is added and the distinct site object/Hom universes are retained.
No fault or STATEMENT-DISPUTED issue was found.

Searches actually run with `msearch.py NB def-weil-proetale-module-direct-image`:

- `leanfinder`: “direct image of constant coefficient module sheaves on small
  pro-etale sites by base change and restriction of scalars”: 8 hits including
  `Scheme.Modules.restrictFunctor`, `SheafOfModules.unitToPushforwardObjUnit`, and
  condensed module constructions; no exact pro-etale specialization among these hits.
- `loogle`: `SheafOfModules.pushforward`: 12 hits, including the generic pushforward,
  its object formula, identity/composition isomorphisms and congruences.
- `leansearch`: “direct image sheaves of modules continuous functor of sites”:
  unavailable, Internal Server Error; not recorded as a negative result.
- `grep`: `def pushforward|pushforward.*[Aa]dditive` in
  `Algebra/Category/ModuleCat`: 12 hits, including generic sheaf and presheaf pushforward.
- `rg` of the old upstream pro-etale `UpperLowerStar/Defs.lean` found the general
  coefficient-category lowerStar, not the ringed-site constant-module specialization.
- `grep -rn` of the item id in old upstream `WeilConjectures` found no occurrence;
  `rg` of `dag/lean_names_upstream.json` for the exact existing declaration found none.
- `rg` of `lean/Sheaf` for `proEtaleConstantModuleDirectImage` found the exact existing
  definition at line 237 of the inverse-image dependency; its complete body was read.

Validation: the mandatory dry run checks the recorded existing declaration on the
server by importing its module and running `#check` in the private compile overlay.
No delivered Lean files need compilation, since none are introduced.

## Second reading by NB

I independently opened the complete node, all four statement-dependency nodes,
their recorded declarations, and the body of
`AlgebraicGeometry.Scheme.proEtaleConstantModuleDirectImage` in
`Sheaf.AlgebraicGeometry.ProEtaleInverseImage`. I read Stacks
`sites-modules.tex`, definition-pushforward (Tag 03D6), including its ambient
morphism-of-ringed-topoi hypothesis, and `proetale.tex`, section-morphism
(Tag 09A5), introductory paragraph. The former defines precisely restriction
of the direct-image module action through the structure homomorphism; the latter
supplies the site morphism for every scheme morphism. Neither imposes a
finiteness, characteristic, or weakly-etale hypothesis on f. I also read the
blueprint source introducing the underived functor before deriving it: its
finite-level coefficient assumptions specialize this general construction.

My object/hypothesis/clause inventory and comparison is:

- Schemes X and Y, and an arbitrary scheme morphism f: the binders
  `{X Y : Scheme.{u}} (f : X ⟶ Y)` use Mathlib's `Scheme` and `Scheme.Hom`,
  whose definitions I read. Verdict: exact, with no extra geometric instance.
- A commutative ring A: `(A : Type u) [CommRing A]`. The dependency
  `proEtaleDerivedCategory` uses this same binder and lifts A to
  `ULift.{u+1,u} A`. Verdict: exact within the explicitly cited size convention;
  no field, nontriviality, torsion, prime, or invertibility condition appears.
- Small pro-etale sites and module categories: `ProEt.topology X` and
  `ProEt.topology Y`, with `SheafOfModules.{u+1}` over the ring-forgotten
  `proEtaleConstantRing`. Unfolding the latter gives exactly the constant
  CommRingCat sheaf in `proEtaleDerivedCategory`. The other dependency,
  `ringedSiteModules`, abbreviates this same Mathlib category. I read
  `SheafOfModules` and `SheafOfModules.Hom`: an abelian-group sheaf with
  sectionwise modules and sectionwise linear natural maps. Verdict: exact;
  this is not a substituted condensed-module-object category.
- Base change u_f, its action on arrows, covers and fibre products:
  `proEtaleBaseChange f` abbreviates
  `MorphismProperty.Over.pullback @WeaklyEtale ⊤ f`;
  `proEtaleBaseChange_isContinuous`, `proEtaleBaseChangeCoverPreserving` and
  `proEtaleBaseChange_preservesFiniteLimits` provide the specified properties.
  The definition uses the variable factor first, matching V ×_Y X.
  Verdict: the recorded dependency supplies precisely the needed data.
- The canonical ring map rho extending constant sections:
  `proEtaleCoefficientDirectImageMap f A` specializes
  `proEtaleConstantDirectImageMap` to the lifted coefficient ring. I read the
  latter's body: the sheafification adjunction extends the whiskering of
  `toSheafify` along `(proEtaleBaseChange f).op`. The direct-image definition
  then whiskers rho with `forget₂ CommRingCat RingCat`. Verdict: exact
  canonical map, with no arbitrary homomorphism or existence choice.
- For every module sheaf F, sections and restrictions:
  `SheafOfModules.pushforward` has underlying presheaf
  `PresheafOfModules.pushforward rho.hom`, whose body is
  `pushforward₀ … ⋙ restrictScalars`. Reading `pushforward₀Obj` gives
  F evaluated at u_f(V), with restrictions `F.map (u_f.op.map a)`.
  Verdict: exactly both section and restriction formulas.
- Underlying abelian direct-image sheaf: `SheafOfModules.pushforward` obtains
  its sheaf field from `F.sheafPushforwardContinuous`; its underlying
  presheaf is the same precomposition as `proEtaleSheafDirectImage`.
  `pushforwardCompToPresheaf` is an identity isomorphism. Verdict: exact.
- The scalar action and compatibility axioms:
  `PresheafOfModules.restrictScalarsObj` applies
  `ModuleCat.restrictScalars (rho.app V).hom` to the original section module.
  Its restriction map retains the old function; its semilinearity uses
  naturality of rho and the original semilinearity. Verdict: the action is
  exactly `(a,s) ↦ rho_V(a) s`, with the required module and restriction laws.
- Every morphism phi and its linearity:
  `pushforward₀.map` has `app V := phi.app _`, and `restrictScalars.map`
  retains these functions. I read `pushforward_map_app_apply`, which states
  the specified component formula, and the restriction-of-scalars body.
  Verdict: precisely phi at u_f(V), linear over A_Y(V) through rho.
- Identities, composition and addition: the functor fields retain the
  original componentwise maps. For addition I independently checked
  `SheafOfModules.add_val`, `PresheafOfModules.add_app`, and the additive
  restriction-of-scalars functor: evaluation after pushforward sends
  phi + psi to phi_(u_f V) + psi_(u_f V). Verdict: the constructed functor
  is additive as stated. A separate bundled `Functor.Additive` witness is
  not part of the definition's return type; no extra theorem is needed
  to identify this existing construction at statement stage.

Edge cases: zero coefficient rings and zero modules are admitted, and the
section formulas send the zero module to zero. Empty schemes and empty
covering families are covered by the unchanged site and sheaf definitions.
There is no index set, n, or characteristic binder to restrict. All universe
variables are bound: schemes use u, site objects u+1 and site Homs u;
sections use u+1. No equality of those two site universes is imposed.
Identity and composite maps use the chosen fibre products; the node does
not ask that those products be literally equal to unchosen alternatives.

Independent searches: `msearch.py ... leanfinder` with query
"ringed site module direct image sectionwise scalar restriction precomposition
functor" returned eight hits, including `SheafOfModules.restrictScalars`,
`PresheafOfModules.pushforward`, and their object formulas.
`msearch.py ... loogle 'PresheafOfModules.pushforward_map_app_apply'` returned
the exact component lemma. I ran rg on Mathlib's module-category sources
for restriction-of-scalars/additive pushforward, and on both the upstream
WeilConjectures tree and the project's lean/Sheaf and pro-etale framework
for direct-image and lowerStar constructions. The exact constant-ring
module-sheaf construction is the recorded existing declaration. I opened
the exact group-clone `FiniteCoefficient.UpperLowerStar.Defs` and
`ModuleObject.UpperLowerStar.Defs` and read `coord/pefw-upstream-framework.md`:
the former supplies the ordinary sheaf precomposition; the latter's
condensed-ring `lowerStar` has different coefficients and category, so its
similar name is not an exact replacement here.

No mathematical or signature mismatch was found. The sandbox has no new
nodes, dependency repairs, statement_change, or delivered Lean modules.
The existing definition has real pushforward data, not sorry or Nonempty
choice. Its original docstring names its owning inverse-image blueprint
node and describes this construction; reusing it does not justify changing
that read-only declaration. The recorded lean.statement is verbatim the
definition's signature up to :=. Nothing correct was rewritten; this
second-reading section is the only change. Server validation is performed
by deliver2.py through scompile.py on its existing-declaration probe.
