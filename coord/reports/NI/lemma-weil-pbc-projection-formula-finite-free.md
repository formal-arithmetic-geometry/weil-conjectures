## Worker report

The module `Sheaf.Paper.ProjectionFormulaFiniteFree` states
`SheafOfModules.ringedProjectionFormula_finiteFree`, with proof `sorry`.
It uses the actual pair returned by
`SheafOfModules.ringedProjectionFormulaArrows` from
`Sheaf.Paper.ProjectionFormulaArrows`, rather than replacing either map by an
arbitrary arrow or asserting only existence of some isomorphism. No definitions,
new nodes, dependency repairs, or statement corrections are introduced.

Hypothesis-by-hypothesis correspondence:

- The context “the maps pi and rho” imports all the data of definition 1264.
  `C,D,JC,JD,R,S,RI,uInv,uPush,adj` and `[PreservesFiniteLimits uInv]`
  specify the small ringed topoi. `I,c,uStar,hobj,hmap` specify module
  pullback by the stipulated extension of scalars, and `V,am` its adjunction.
  The additive instances are the additive structures of these module functors.
- The two `HasDerivedCategory.{w}` instances give the unbounded derived
  categories. `LF,epsilon,hLF,computeL` specify the total left derived
  pullback and its K-flat flat-term computation. `PR,PS,hPR,hPS` identify
  the K-flat flat-term representatives exactly, with no chosen substitute
  class. `TR,TS,rR,rS` give the derived tensor functors and their resolution
  identifications. `k` is the canonical ordinary pure-tensor comparison,
  from which the dependency constructs the canonical derived comparison.
- `RF,eta,hRF,computeR` specify the total right derived direct image and
  its computation on K-injectives. `adjD,canonicalAdj` stipulate the
  canonical derived adjunction from the ordinary module adjunction.
- `E` is arbitrary in D(S). `K,hK,repE` are its K-injective representative,
  exactly as in the dependency's construction. These are representative
  data for the specified arrows, not an additional restriction on E.
- `F,P,hbounded` are the bounded coefficient complex, its strict-perfect
  package, and boundedness from definition 1264. Finite-free coefficients
  admit such a package (the identity splitting in degree -a, zero elsewhere).
  The statement allows any valid package for this same complex, since the
  finite-total inverse is uniquely determined by the ordinary total mate.
- `N : ℕ`, `a : ℤ`, and `hfree` render precisely F=R^N[a]. The right-hand
  side of `hfree` is `HomologicalComplex.single _ (ComplexShape.up ℤ) (-a)`
  evaluated on the product of `Fin N` copies of `SheafOfModules.unit` of R.
  In an additive module category this finite product is the finite sum R^N.
  This is the complex concentrated in degree -a with zero differential,
  the usual cohomological shift of R^N by a. No boundedness or splitting
  condition beyond the context needed to invoke the recorded arrows is added.

Clause-by-clause correspondence: `.1` of the recorded pair is pi and `.2`
is rho. The first conjunct `.1 ≫ .2 = 𝟙 _` is rho after pi, i.e.
rho*pi=1 on Rh_*E tensor F. The second conjunct `.2 ≫ .1 = 𝟙 _` is
pi after rho, i.e. pi*rho=1 on Rh_*(E tensor Lh^*F). Each occurrence uses
identical ringed, representative, coefficient, and package data. No `let`
occurs in the signature and no local notation or local instance is used.
All variables and universes are explicitly bound.

The dependency module and its full recorded declaration/docstring were read.
Its first component is the canonical counit mate using the characterized tensor
comparison; its second is the localization of the specified finite-total chain
inverse, conjugated by the canonical representative isomorphisms. Thus the
pair used in the conclusion is precisely the pair in the node, including the
specified inverse construction. The module docstring and theorem docstring cite
blueprint lemma 1265; the latter gives all five expanded DAG proof steps and
their dependencies. The source blueprint lemma and definition 1264 were read.

Proof imports: `Mathlib.Algebra.Homology.BifunctorShift`
(`CochainComplex.mapBifunctor`), `Sheaf.CategoryTheory.ModulePullbackTensorIso`
(`SheafOfModules.module_pullback_tensor_iso`),
`WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`,
`Mathlib.CategoryTheory.Adjunction.Limits`
(`CategoryTheory.Adjunction.rightAdjoint_preservesLimits`),
`Sheaf.Algebra.Homology.KFlatResolutionGeneral`,
`Sheaf.Algebra.Homology.KFlat`,
`Sheaf.Paper.RingedTopoiCanonicalTensorPullback`, and
`Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`. The arrow module
is a public import. `Mathlib.Algebra.Homology.Single` supplies the single complex.

Edge cases: N=0 is allowed by `Fin N` (the empty product/zero module), a=0
is degree zero, positive and negative shifts are all covered by `a : ℤ`.
E=0, zero ring sheaves and trivial/empty sites are not excluded. No nonempty
index, nonzero rank, torsion, properness, or boundedness restriction on E is
imposed. The site and derived universes are exactly those of the recorded
arrow definition; no additional universe equality is imposed.

Searches for an existing statement:

- `msearch.py leanfinder`, query “finite free shifted coefficient projection
  formula derived ringed topos inverse maps”: eight hits in module-sheaf free
  objects and unit Hom equivalences, none states these derived inverse equations.
- `msearch.py loogle`, query `CategoryTheory.Adjunction, "tensor"`:
  ten hits on monoidal unit/counit identities, rigid tensor adjunctions and
  tensor-Hom adjunctions, none this statement.
- `msearch.py grep`, query `projectionFormula|projection_formula` in
  Mathlib/CategoryTheory: zero hits.
- `rg` of that pattern and `ProjectionFormula` in the upstream project and
  `lean/Sheaf`: generic or scheme-specific projection formulas, plus the
  dependency's arrow constructions, but no statement of these two identities
  for the specified general ringed-topos maps and shifted finite-free F.
- Exact item-id search in upstream WeilConjectures: no hits.

Validation: compile every delivered module through the prescribed `scompile.py`;
the dry run uses `deliver2.py --no-push`. No delivery is pushed by this worker.

Tool note: the installed `scompile.py` currently tries `nt_local_compile.run`
before server fallback, contrary to the supplied server-only instructions.
The first wrapper invocation was stopped after inspection revealed this change.
Subsequent validation calls `scompile.run_server` directly; the dry-run wrapper
redirects `scompile.run_many` to that same existing server entry point in memory.
No launcher script is modified. Server compilation retains nice 19 and the
standard per-file 60-second limit.

Server result: `ProjectionFormulaFiniteFree.lean` compiled cleanly in 13.8 s,
with nice 19, two threads and the standard 60 s limit; no warnings or errors.
All thirteen side-only prerequisite modules compiled in the private server overlay.

## Second reading by NI

Independent second reader, 2026-10-15. I opened the item JSON, its blueprint
source (lemma 1265), definition 1264 both in the blueprint and the expanded DAG,
and the full signatures and implementation of the recorded
`Sheaf.Paper.ProjectionFormulaArrows`. The inherited context is essential here:
this is a claim about that particular pair, not existence of inverse arrows.
The source is a blueprint lemma, not a Stacks lemma with the same name. I also
read the cited Stacks source hypotheses: 0038 in categories.tex (right adjoints
preserve existing limits), 03EL in sites-modules.tex (module pullback tensor
comparison), 06YS and 07A4 in sites-cohomology.tex (K-flat resolutions and derived
pullback tensor comparison), and 0FND in derived.tex (derived adjunction).
These assume the indicated ringed sites/topoi and derived constructions, not
properness, Noetherianity, a field, or boundedness of E.

My object/hypothesis/conclusion inventory and Lean correspondence:

1. A morphism of small ringed topoi, target ring R (Lambda in the item), source
   ring S: `C,D,JC,JD,R,S,RI,uInv,uPush,adj`, finite-limit preservation,
   `I : AlgebraicInverseImage ...`, and `c : RI ⟶ S`. The site object and
   morphism universe is the chosen small universe u, as in definition 1264;
   `w` independently supplies the derived-category universe. I read the size
   convention node: small skeletons are taken in a chosen larger bound. No
   new universe equation has been added by this theorem. Verdict: matches.
2. Ordinary extension-of-scalars module pullback and its right adjoint:
   `uStar,hobj,hmap,V,am`, with their additive structures. `hobj` and `hmap`
   specify the actual dependency's pullback, not an arbitrary additive functor.
   These binders reproduce the dependency signature. Verdict: matches.
3. Unbounded derived module categories, K-flat computed pullback/tensor,
   K-injective computed direct image, and canonical derived adjunction:
   the two `HasDerivedCategory.{w}` instances; `LF,epsilon,hLF,computeL`;
   `PR,PS,hPR,hPS,TR,TS,rR,rS,k`; `RF,eta,hRF,computeR,adjD,canonicalAdj`.
   In particular `hPR,hPS` are equivalences with K-flat flat-term complexes,
   not a stronger selected class. The same exact data are required by the
   recorded arrows. Verdict: matches the inherited construction context.
4. An arbitrary E in D(S): `E`, with `K,hK,repE` specifying a K-injective
   representative. These are the representative choices in definition 1264;
   there is no boundedness or finiteness hypothesis on E. Verdict: matches.
5. A bounded strict-perfect coefficient complex: `F,P,hbounded`.
   I opened `StrictPerfectCoefficientPackage`: its fields are the degreewise
   finite rank, inclusion, projection and splitting identity, with no chain-map
   assumption on the splittings. Its package and boundedness are precisely
   the inputs of the arrows, and are available for a single free complex.
   The claim holds for every supplied package, not just a specially selected
   splitting. The inverse in the dependency is uniquely determined by the
   ordinary total mate, so arbitrary valid packages do not alter the claim.
   Verdict: matches.
6. Finite rank and arbitrary shift, F=R^N[a]: `N : ℕ`, `a : ℤ`, and `hfree`.
   `HomologicalComplex.single ... (-a)` has its given free module in degree
   -a, zero objects elsewhere, and zero differential. I checked
   `single_obj_X_self`, `isZero_single_obj_X`, and `single_obj_d` in Mathlib's
   Single.lean. The `Fin N` product of `SheafOfModules.unit` is R^N; finite
   products and finite sums agree in this additive module category.
   This is exactly the cohomological shift convention. Verdict: matches.
7. rho composed after pi is the source identity: the first conjunct uses
   `.1 ≫ .2 = 𝟙 _`. pi composed after rho is the target identity: the second
   conjunct uses `.2 ≫ .1 = 𝟙 _`. All four calls have identical arguments.
   I checked the dependency's returned types: the source is
   `TR.obj (RF.obj E, DerivedCategory.Q.obj F)` and the target is
   `RF.obj (TS.obj (E, LF.obj (DerivedCategory.Q.obj F)))`. Its first arrow
   is the upstream right-adjoint counit projection mate using the canonical
   tensor comparison; its second is `eB.hom ≫ Q.map s ≫ eC.inv`, with `s`
   the specified finite-total inverse and its recorded summand formula.
   Verdict: both equations concern the correct maps and correct objects.

Edge cases checked independently: N=0 gives the empty finite product, hence
zero in the module category, and is not excluded. a=0 and either sign of a
are allowed. E=0, zero rings, empty sites and sites presenting the empty scheme
are not excluded. Characteristic is unrestricted. The two universes u,w are
bound explicitly; there is no independent too-small test-algebra universe.
The theorem has no local notation, private definition, or local instance and
its signature uses no hidden `let` or `show` binder. It introduces only one
named theorem with proof `sorry`, and no data definition. Its docstring records
all five proof steps, including the chain-map signs, representative comparison
and localization of both inverse equations. No new node or dependency module
is delivered, and there is no statement correction requiring a citer audit.

Independent searches (different queries from the first reader):

- LeanFinder via msearch: “Derived pushforward commutes with tensor product by
  a shifted finite rank free sheaf”. Eight hits, for sheaf pushforward natural
  isomorphisms and the underived free-unit Hom equivalence; none states these
  inverse identities.
- Loogle via msearch: `"projection", "Iso"`. Nine hits on orthogonal projections
  and linear isometries, none on this derived statement.
- LeanSearch via msearch: “The canonical derived projection morphism and finite
  total inverse are mutually inverse for a finite free coefficient complex”.
  Service returned Internal Server Error; recorded as unavailable.
- Independent rg in Mathlib/CategoryTheory, upstream WeilConjectures/CategoryTheory
  and project lean/Sheaf/Paper for `projectionMap`, `projection_formula`,
  `projectionFormula`, `ProjectionFormula`: found the generic upstream mate and
  its compatibility/shift lemmas, the scheme projection formula imports, and
  the recorded arrow definition. I opened ProjectionMap.lean and the local
  derivedProjectionFormulaMate wrapper. The generic upstream statement is a
  construction of a mate (and special invertibility criteria), not these two
  equations for the ringed-topos finite-total inverse. No exact existing match.

No mathematical or Lean-signature mismatch found; no Lean changes needed.
The node's recorded signature agrees verbatim with the declaration before
`:= sorry` (including its multiline formatting). The worker report's old
server-only tool note is superseded by the human's 2026-10-15 authorization:
this reading invoked the normal scompile.py entry point without monkeypatching
or bypassing local compilation. It compiled the delivered module cleanly in
17.5 seconds (sandbox check 10.9 seconds), with no errors or warnings.
