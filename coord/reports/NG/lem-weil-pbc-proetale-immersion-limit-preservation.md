## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation` states
`AlgebraicGeometry.Scheme.proEtale_immersion_inverseImage_preservesLimits`.
Its only theorem has proof `sorry`; there are no new definitions or postponed helper
lemmas. The docstring gives the node's seven-step proof, including affine closed
adjunction, open slice restriction, Zariski gluing, composition, algebraic structures,
module limits and scalar transport through a ring isomorphism.

Hypothesis and clause matching:

- Schemes X and Y are `{X Y : Scheme.{u}}`; the specified arrow is `(f : Y ⟶ X)`.
  `[IsImmersion f]` is exactly closed immersion followed by open immersion, by
  Mathlib `AlgebraicGeometry.isImmersion_iff_exists` (Immersion.lean, lines 151–158).
- The sites are precisely `ProEt.topology X` and `ProEt.topology Y`, using the
  dependency's `proEtaleSheafInverseImage` and `proEtaleModuleInverseImage`.
  No replacement category or bound on scheme objects is introduced.
- The first two conjuncts are `PreservesLimitsOfSize.{u+1,u+1}` for the specified
  inverse image with values in `Type (u+1)` and `AddCommGrpCat.{u+1}`. This is every
  small limit relative to the fixed sheaf universe, not just products or finite limits.
- `∀ R : Sheaf (ProEt.topology X) CommRingCat.{u+1}` supplies every commutative
  ring sheaf, without a constant-coefficient restriction.
- For the canonical module inverse-image functor, the existential additive instance,
  `PreservesFiniteLimits`, `PreservesFiniteColimits` and `PreservesLimitsOfSize`
  give additivity, exactness and all small limits. In abelian categories additive
  finite-limit/finite-colimit preservation is exactly preservation of kernels and
  cokernels, hence exactness. These are conclusions, not assumed properties.
- The `Nonempty` natural isomorphism identifies the functor followed by
  `SheafOfModules.toSheaf` with that forgetful functor followed by abelian inverse
  image. It specifies the underlying abelian sheaves on morphisms as well as objects.
- `eR` and `eM` are underlying-set natural comparisons for ring and module inverse
  image. The subsequent graph condition quantifies over every test sheaf T and every
  triple of generalized sections `(a,b,t)`. If t=a•b, their inverse images satisfy
  the same identity under eR and eM. Taking T to be the product of the operand
  sheaves and a,b the projections gives precisely the finite-product comparison
  formula for the action. Conversely that formula gives all these graph identities.
  Thus this condition is not limited to global sections.
- The final clause quantifies over every target ring sheaf S and every ring-sheaf
  isomorphism c. Its functor P has object equality `hobj` with the dependency's
  `SheafOfModules.changeOfRings c.hom` applied to canonical inverse image, and its
  maps are exactly `changeOfRingsHom` applied to inverse-image maps, transported
  along hobj. P therefore denotes the specified tensor-extension functor, with no
  arbitrary map or unrelated exact functor substituted.
- The final additive, finite-limit, finite-colimit and all-small-limit conclusions
  express exactness and limit preservation after that extension. Countable products
  are included as limits of discrete diagrams on `ULift ℕ` in universe u+1.
- There is no Noetherian assumption. The last clause requires an isomorphism c;
  nothing is asserted for scalar extension along a noninvertible ring map.

Dependency declarations inspected and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, together with the equivalent immersion
  factorization from `Mathlib.AlgebraicGeometry.Morphisms.Immersion`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`; its actual site is
  `Scheme.ProEt` / `Scheme.ProEt.topology`, as retained here (no derived category
  is needed in this underived statement).
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`:
  `AlgebraicGeometry.Scheme.proEtaleSheafInverseImage` and
  `AlgebraicGeometry.Scheme.proEtaleModuleInverseImage`, with the actual base-change,
  ring adjunction unit and AsSmall transport read in full. Module inverse image is
  over the inverse-image ring and not over an arbitrarily chosen target ring.
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`: the recorded general site
  and sheaf framework (`CategoryTheory.Sheaf`; the recorded H' is irrelevant here).
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the transparent abbreviation for Mathlib `SheafOfModules` used in the signature.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`:
  `SheafOfModules.changeOfRings` and `SheafOfModules.changeOfRingsHom`; the
  sectionwise tensor construction, restriction maps and sheafification were read.

Proof imports include all recorded project proof modules: site morphism composition,
abelian exactness, abelian underlying comparison and weakly etale localization.
The Mathlib limit/adjunction modules provide the sectionwise sheaf/module limits and
right-adjoint preservation inputs. The affine-closed extra-adjoint node has no recorded
Lean module yet, so there is no import for it; it is a proof dependency, not an object
needed to state this theorem. No statement prerequisite is missing or duplicated.
The 51-module framework and `coord/pefw-upstream-framework.md` were inspected; its
module-object coefficient category is not substituted for general ring-module sheaves.

Source check: local `literature/stacks-project/proetale.tex`,
`lemma-closed-immersion` (Tag 09AA) explicitly says closed inverse image commutes with
limits and reduces the proof Zariski-locally to the affine case. The open and module
extensions follow the source places recorded in the node; they do not impose extra
hypotheses. No statement correction or disputed statement was necessary.

Edge cases: the empty scheme and identity/open/closed immersions are all allowed.
The empty diagram is included in all-limit preservation. Zero module, zero ring
and arbitrary ring-sheaf isomorphisms (including identity) remain allowed. No affine,
quasi-compactness, characteristic or Noetherian restriction was added. Schemes live in
u, their pro-etale sites retain object universe u+1 and Hom universe u, and sheaf
values/modules and small diagrams live in u+1. Thus no site universe is forced equal
to its smaller Hom universe. The scalar condition uses arbitrary test sheaves, so
failure of global sections to detect sheaf maps does not weaken the action assertion.

Searches for an existing statement:

- `msearch.py ... leanfinder "Inverse image along a locally closed immersion on the
  pro etale site preserves all small limits of sheaves"`: eight hits, seven about
  forgetful functors preserving scheme/ringed-space pullbacks and one generic
  `Functor.sheafPullbackConstruction.preservesFiniteLimits`; none supplies this theorem.
- `msearch.py ... loogle "Sheaf, PreservesLimits"`: zero hits, unknown identifier
  `Sheaf`; no usable match.
- `msearch.py ... grep "proetale.*closed|closed.*proetale|inverseImage.*[Ll]imits"`:
  seven unrelated object-property inverse-image limit/colimit closure results.
- `rg` in slopmaster2 `WeilConjectures`, group `lean/WeilConjectures` and `lean/Sheaf`
  for immersion/limit patterns found affine-transition limit theorems and Zariski
  module restriction results, not this pro-etale inverse-image statement. The exact
  node id has no source hit. The upstream name index also has no exact-node-id hit.
- Additional local search for `changeOfRingsFunctor`, change-of-rings functoriality
  and inverse-image underlying comparisons found no existing general functor for
  this exact tensor construction. Rather than create a duplicate notion, the theorem
  states functor existence with the existing object and morphism constructions fixed.

Validation: initial elaboration found `Scheme.forget` shadowing the categorical
forget functor; all occurrences now use `CategoryTheory.forget`. The supplied
`scompile.py` currently attempts its local mirror before server fallback, despite
this task's server-only requirement; this was discovered after the initial invocation.
Final validation therefore calls `scompile.run_server` directly, with the same module,
60-second per-file limit, nice 19 and two threads. The dry-run delivery also uses the
server preflight and server compiler. No compiler was invoked directly and no Lake
build was requested. All project edits are confined to this item's sandbox.


## Second reading by NG

Independent second reading, 2026-10-15. I read the node, its complete seven-step
proof, the delivered signature, the recorded statement-dependency signatures and
source implementations, and the Stacks source before accepting the statement.
No mathematical or Lean-source repair was needed; this reading adds this audit.
The worker report above is retained.

Object/hypothesis/conclusion checklist (each verdict is pass):

1. Arbitrary schemes X,Y and the specified arrow u:Y→X are `{X Y : Scheme.{u}}`
   and `(f : Y ⟶ X)`. Mathlib's `Scheme` is the locally affine locally ringed
   space definition. There is no implicit affine, separated, finite-type,
   Noetherian, quasi-compactness, nonemptiness or characteristic assumption.
2. Locally closed immersion is `[IsImmersion f]`. I opened Mathlib
   `Morphisms/Immersion.lean`: `isImmersion_iff_exists` says precisely closed
   immersion followed by open immersion, with composite equal to f. The closed
   factor is the recorded `IsClosedImmersion`, a closed embedding surjective
   on stalks. Thus this is the factorization in the node, not an open-only case.
3. The small pro-etale sites are `ProEt.topology X` and `ProEt.topology Y` on
   `X.ProEt` and `Y.ProEt`. I read `ProEtaleDerivedCategory` and the inverse-image
   dependency's `proEtaleBaseChange`, `proEtaleSheafInverseImage`, its adjunction,
   and the AsSmall transports. The former is actual weakly-etale base change;
   the latter is Mathlib left Kan extension followed by sheafification, with
   the required direction X-sheaves to Y-sheaves for this f. The module functor
   uses the ring adjunction unit, transports through the equivalent small
   model, and returns to these same sites. No replacement site is introduced.
4. All small limits of sets and abelian sheaves are the first two
   `PreservesLimitsOfSize.{u + 1, u + 1}` conjuncts, respectively with
   `Type (u + 1)` and `AddCommGrpCat.{u + 1}`. The fixed sheaf universe is u+1.
   Both the objects and morphisms of the indexing category range in this
   universe; these are all limits, not merely finite or countable limits.
5. Every commutative ring sheaf is `∀ R : Sheaf (ProEt.topology X)
   CommRingCat.{u + 1}`. The source and target module categories of the recorded
   `proEtaleModuleInverseImage f R` are exactly modules over R and f⁻¹R,
   forgetting commutativity only to use Mathlib `SheafOfModules`. I opened
   `RingedSiteModules`: its abbreviation is this same Mathlib category, not
   another module notion. The existential additive instance is a conclusion;
   `PreservesFiniteLimits` and `PreservesFiniteColimits` express exactness,
   and `PreservesLimitsOfSize` gives every small limit.
6. The underlying abelian sheaf clause is the natural functor isomorphism
   `Nonempty (proEtaleModuleInverseImage f R ⋙ SheafOfModules.toSheaf _ ≅
   SheafOfModules.toSheaf _ ⋙ proEtaleSheafInverseImage f AddCommGrpCat)`.
   This includes morphisms, not merely a collection of object isomorphisms.
7. The scalar action clause is the existential `eR`, natural `eM`, and the
   subsequent universally quantified graph identity. For every test sheaf T,
   maps a:T→R and b,t:T→M satisfying t=a•b are carried to the corresponding
   action identity after these comparisons. This is precisely action transport:
   take T to be the product of the underlying R and M sheaves, a and b its
   projections and t its action map; the displayed implication gives the
   finite-product comparison formula. Conversely that formula, precomposed
   with any pair (a,b), gives the displayed graph condition. Testing all T
   avoids the invalid inference from global sections alone.
8. Arbitrary target ring sheaf S and ring isomorphism c:f⁻¹R≅S are the final
   universal binders. I read `changeOfRingsPresheaf`, `changeOfRings`, and
   `changeOfRingsHom` in the recorded tensor dependency: sections are scalar
   extension by tensor product, then sheafification, and maps are sheafified
   id⊗a. The existential functor P has object equality `hobj` with this tensor
   construction, and its map equality fixes precisely the corresponding
   `changeOfRingsHom`, conjugated by those object equalities. It cannot be an
   unrelated exact functor. Its finite-limit and finite-colimit preservation
   express exactness and its all-limit preservation includes countable
   products (the discrete diagram indexed by ULift ℕ). Additivity here follows
   from exactness in these abelian categories and imposes no stronger claim.
9. The qualifier about c is respected: c is an isomorphism, and the statement
   asserts nothing about arbitrary noninvertible scalar-extension maps.
   Quantifiers have the same order as the node: schemes, immersion, every R,
   its properties, then every S and c and the specified tensor functor.

Source reading: `proetale.tex`, `lemma-closed-immersion` (09AA), clause (1),
says inverse image for any closed immersion commutes with limits. Its proof
explicitly localizes on X in the Zariski topology, then invokes
`lemma-closed-immersion-affines-apply` (09BL), whose (3) is the extra left
adjoint. Neither statement assumes Noetherianity. The neighboring finite-map
lemma's finite-presentation assumption is not an assumption on this lemma.
I also read `sites-modules.tex`, `lemma-pullback-module` (03D2): applying exact
set inverse image to the action gives the module over the inverse-image ring;
`lemma-limits-colimits` (03DB) states that module limits and colimits are
preserved by forgetting to abelian sheaves. Open restriction and composition
are the node's specified extensions. The seven numbered proof paragraphs in
the theorem docstring retain the complete node argument, including Zariski
gluing of inverse comparisons, componentwise algebraic operations, linearity
of inverse limit comparisons, and the balancing computation for c.

Edge cases: empty X or Y, identity/open/closed immersions, the zero ring and
zero module, the empty diagram and countable diagrams all remain admitted.
There is no n or prime/characteristic binder to restrict. Identity c and every
ring-sheaf isomorphism are covered. The original site has object universe u+1
and Hom universe u; the AsSmall dependency only enlarges Homs for the module
API and returns to that site. No equality between those universes is imposed.
Values and diagrams use the fixed u+1 sheaf universe as the node requires.

Independent H4 searches used different wording from the worker:

- LeanFinder: “Restriction of pro-etale sheaves to locally closed subschemes
  commutes with arbitrary limits and products”: eight hits, concerning affine
  transition limits, topological sheaf equalizers and Zariski module restriction
  composition. None states this inverse-image theorem.
- Loogle: `"sheafPullback", "PreservesLimits"`: zero hits.
- LeanSearch: “The inverse image on proetale sheaves along an immersion
  preserves arbitrary limits”: unavailable (Internal Server Error), recorded
  as unavailable rather than a negative search result.
- Search-service grep: `immersion.*preservesLimits|preservesLimits.*immersion|
  proEtale_immersion`: zero hits. Independent rg on Mathlib, upstream
  WeilConjectures, group-clone WeilConjectures and project Sheaf using
  immersion/inverseimage/upperstar/proet/limit combinations found no duplicate.
  The pro-etale lowerStar all-limit instances concern direct image. I opened
  the exact group-clone ModuleObject/UpperLowerStar/Defs declarations: their
  condensedRingObj module objects and upperStar extension along a condensed
  coefficient map do not supply the arbitrary-ring-sheaf theorem here. I read
  coord/pefw-upstream-framework.md; this conclusion uses the 51-module
  framework in the group clone, not an inference from the old checkout.

H5/H6/H8/H9: the only declaration in this delivery is the named theorem with
whole proof `by sorry`; no definitions or helper proofs are added. There are
no new or repaired dependency nodes/modules to audit under H12/H13, and no
statement correction or citer audit is necessary. The affine extra-adjoint
node remains an unstated proof dependency, not a missing object in this
signature. All already recorded project proof modules are imported. Every
variable and universe is bound, all lines are at most 100 characters, both
source/blueprint docstrings are present, and the node's `lean.statement` was
checked by exact string equality against the complete file signature.

Validation: server compilation through `scompile.run_server` passed cleanly;
the delivered file took 3.0 seconds, nice 19, two threads, 60-second limit.
No local compiler or library build was run. Because the installed scompile
CLI and deliver2.run_many first attempt a local compiler, the delivery calls
bind `scompile.run_many = scompile.run_server` before invoking the unchanged
deliver2 main, enforcing the human's server-only requirement for the dry run
and actual delivery too. Only the review report changed in this second reading.
