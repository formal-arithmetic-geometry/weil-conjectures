## Worker report

The module `Sheaf.AlgebraicGeometry.CoherentStalkMapExtends` states
`AlgebraicGeometry.exists_open_hom_of_coherent_stalk_map`. It uses the Mathlib
notion `IsLocallyNoetherian X`, the project coherent predicate
`RingedSpace.IsCoherent X.toRingedSpace F`, and the Mathlib stalks of the
underlying additive presheaves. A stalk homomorphism is represented as a linear
map over the stalk of the structure sheaf.

The hypotheses render as follows. `{X : Scheme.{u}} [IsLocallyNoetherian X]`
is the locally Noetherian scheme hypothesis. `(F G : X.Modules)` are the two
sheaves of modules. `hF` and `hG` state that both modules are coherent. `x :
X.carrier` is the chosen point. `ψ` is an
`X.ringCatSheaf.presheaf.stalk x`-linear map from the stalk of `G` to the stalk
of `F`.

The conclusion is `∃ U : X.Opens, x ∈ U`, followed by a morphism `φ` between
the restrictions of `G` and `F` along `U.ι`. For every element `m` of the
stalk of `G`, the final equality says that `ψ m` equals the map induced by
`φ` on the restricted stalk, transported to and from the original stalks by
`Scheme.Modules.restrictStalkNatIso`: the inverse component for `G`, then the
additive stalk functor applied to `φ.mapPresheaf`, then the hom component for
`F`.

Dependency declarations used:

- `pqf-def-locnoeth`: Mathlib `AlgebraicGeometry.IsLocallyNoetherian` in
  `Mathlib/AlgebraicGeometry/Noetherian.lean`.
- `pqf-def-coherent`: `AlgebraicGeometry.RingedSpace.IsCoherent` in
  `Sheaf.AlgebraicGeometry.Coherent`.
- `def-weil-pbc-module-stalk`: Mathlib `TopCat.Presheaf.stalk` and the stalk
  module instance from `PresheafOfModules` in
  `Mathlib/Algebra/Category/ModuleCat/Stalk.lean`.
- `def-weil-sheaf-of-modules-category`: Mathlib `Scheme.Modules` and its
  morphisms in `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`.

Edge cases checked: the neighbourhood is required to contain `x`; the stalk
map is stated for arbitrary elements, including the zero element; no
nonemptiness, separation, or finite-type hypothesis beyond local Noetherianity
and coherence is added; the restriction stalk comparison explicitly handles
the subtype point `⟨x, hx⟩`.

Searches made:

- `msearch.py ... leanfinder "map of stalks of coherent modules extends to a morphism on an open neighbourhood"`: returned only affine tilde/stalk declarations (`ModuleCat.Tilde.toOpen_germ_apply`, `toStalk`, etc.), no exact match.
- `msearch.py ... loogle "TopCat.Presheaf.stalkFunctor, Scheme.Modules.restrictStalkNatIso, IsCoherent"`: zero hits because `Scheme.Modules.restrictStalkNatIso` was not indexed.
- `msearch.py ... grep "coherent.*stalk.*map" WeilConjectures`: zero hits.
- `rg` over the source and project for the node id and theorem name: no existing declaration or duplicate module.
- The node's recorded Mathlib searches were also checked: LeanFinder and grep found stalk infrastructure only, with no theorem extending arbitrary coherent stalk maps.

## Earlier second reading (a previous round; superseded)

I reread the node statement and the module signature clause by clause. The
local-Noetherian instance, two coherent-module hypotheses, point, and arbitrary
stalk-linear map all occur verbatim. The existential open and membership
condition occur before the restricted module morphism. The final universal
clause is an equality for every stalk element and uses the inverse restricted
stalk isomorphism for `G`, the stalk map of `φ`, and the forward restricted
stalk isomorphism for `F`, exactly the canonical transport needed to compare
stalks over the open with stalks on `X`. The module compiles cleanly with only
the theorem's expected `sorry` warning, and no changes were needed after this
reading.

## Second reading by H1

Read the repository node, sandbox node and complete Lean module independently.
The Stacks sources are absent from this clone's literature directory; I read
`/home/ubuntu/c1-stacks-review/coherent.tex` at lines 2220–2250 and 2391–2407,
and `/home/ubuntu/c1-stacks-review/modules.tex` at lines 3618–3695. The former
explicitly assumes a locally Noetherian scheme and two coherent modules in
01Y4; no ambient field, separation, finite-type morphism, or characteristic
assumption is implicit. The sandbox has no statement correction and no new
nodes or dependency modules.

Object/hypothesis/conclusion inventory, with the Lean counterpart and verdict:

1. Scheme X: `{X : Scheme.{u}}`, an arbitrary scheme, agrees.
2. Local Noetherianity: `[IsLocallyNoetherian X]`, agrees with
   `pqf-def-locnoeth`. Opened Mathlib Noetherian.lean:57 and its recorded
   affine-cover characterization; the every-affine-open formulation is
   equivalent to the node's affine-cover formulation.
3. O_X-modules F and G: `(F G : X.Modules)`, agrees. Opened Mathlib
   Modules/Sheaf.lean:38–49 and ModuleCat/Sheaf.lean:33–54: `Scheme.Modules`
   is precisely `SheafOfModules` for the structure ring sheaf, and its Hom
   is a morphism of presheaves of modules. This specializes the recorded
   declaration of `def-weil-sheaf-of-modules-category` to the Zariski site.
4. Both coherent: `hF` and `hG` use `RingedSpace.IsCoherent X.toRingedSpace`,
   agrees. Opened `pqf-def-coherent` and Coherent.lean in full: finite type
   and finite-type kernels of every map from finite free modules on every
   open, exactly the Stacks predicate. This is not the upstream predicate
   `Scheme.Modules.isCoherent` meaning quasi-coherent plus finite presentation.
5. Point x: `(x : X.carrier)`, agrees; no genericity or closedness condition.
6. Arbitrary O_{X,x}-linear map G_x to F_x: the `ψ` binder uses the
   additive-presheaf stalks of G and F, in that order, and a LinearMap over
   `X.ringCatSheaf.presheaf.stalk x`, agrees. Opened the recorded module-stalk
   dependency and Mathlib ModuleCat/Stalk.lean:155–180: the inferred module
   structure is the colimit module with germ scalar multiplication, not an
   extra assumption or arbitrary module structure.
7. Open neighbourhood: `∃ (U : X.Opens) (hx : x ∈ U)`, agrees. Membership
   precedes the restricted morphism and supplies its subtype point.
8. O_U-linear morphism G|U to F|U: the existential `φ` uses
   `Scheme.Modules.restrictFunctor U.ι`, agrees. Opened its definition in
   Modules/Sheaf.lean:340–351: it evaluates on the open image and transports
   scalars by the open-immersion structure-sheaf isomorphism, the ordinary
   restriction required by the node, not a different module pullback.
9. Induced stalk map equals ψ: `∀ m, ψ m = ...`, agrees. Opened
   `restrictStalkNatIso` and its germ formulas at lines 510–533. The inverse
   component for G sends an original germ to a restricted germ; the stalk
   functor on `φ.mapPresheaf` applies φ to that germ; the hom component for F
   returns it to the original stalk. Thus the displayed composite is exactly
   φ_x under the canonical identifications. Equality on every element is
   equality of the linear maps, with no weaker or stronger clause.

Edge cases: the empty scheme has no x, so the universally quantified statement
is vacuous exactly as in 01Y4. U cannot be empty because hx is required. Zero
modules and the zero linear map are included, with no nonzero hypothesis.
There is no index set, integer n or characteristic parameter in the signature;
finite presentations of rank zero remain permitted in the proof and coherent
predicate. The arbitrary universe u is declared explicitly. Scheme.Modules
uses Mathlib's common scheme/module universe; any pair of modules and scheme
can be put in a common larger universe, and no fixed small universe or testing
universe is imposed. No variable or universe is unbound.

Independent searches (recorded by msearch.py in searches.jsonl):

- LeanFinder: `a linear homomorphism between germs of finitely presented
  sheaves is represented by a local sheaf morphism`. Eight hits: presentation
  maps and `SheafOfModules.IsFinitePresentation`, none an extension theorem.
- Loogle: `TopCat.Presheaf.stalk, LinearMap`. One hit,
  `AlgebraicGeometry.StructureSheaf.toStalkₗ`, a map from a module to its
  associated-sheaf stalk, not extension of arbitrary stalk homomorphisms.
- Mathlib grep: `(stalk.*(extend|neighbo|coher))|((extend|neighbo|coher).*stalk)`.
  Five hits, none exact. Opened SpreadingOut.lean:196–208: the closest hit
  `spread_out_unique_of_isGermInjective` concerns equality of scheme morphisms,
  not existence of a module morphism representing a stalk homomorphism.
- Independently ran rg over WeilConjectures and repository lean/Sheaf for the
  theorem name and stalk/extension/neighbourhood/coherence combinations.
  Hits concern zero/support, surjectivity near a point, tensor products and
  other stalk infrastructure; none states this existence theorem. The
  existing CoherentLocalIsomorphism module concerns properties of an already
  supplied sheaf morphism. No duplicate definition or theorem is needed.
  The worker and node already record the third search family, LeanSearch.

Mismatches and repairs: H8, the original theorem docstring only mentioned finite
presentation and the internal-Hom stalk identification, omitted taking a germ
representative and identifying its induced stalk map, and left a parenthesis
unclosed. Replaced it with all three DAG proof steps, including their dependency
ids and explicit source places. Added the standard copyright/license/authors
header (H9). The mathematical signature, node statement, dependencies and
lean.statement are unchanged; no notion was copied and nothing was proved.
Only the named theorem's `sorry` remains. All imports supply notions used by
the signature. The module and declaration docstrings carry the exact blueprint
id; all lines are within 100 characters.

Verification: scompile.py compiled the revised module on the server in 1.9 s,
exit code 0, with no errors or warnings. A direct string comparison confirms
that the signature is verbatim equal to the node's lean.statement; a line-length
check confirms every Lean line is at most 100 characters.
