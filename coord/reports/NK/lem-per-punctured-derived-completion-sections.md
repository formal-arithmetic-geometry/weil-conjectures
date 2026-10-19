## Worker report

The module `Sheaf.Paper.PuncturedDerivedCompletionSections` states
`AlgebraicGeometry.PuncturedCompletion.punctured_derivedCompletion_sections`.
Only this theorem has `sorry`. All auxiliary objects and maps have concrete data;
functor, naturality, additivity and chain-map fields are checked proofs. No statement
correction, new independent definition node, or dependency repair is needed.

Source read: `literature/stacks-project/algebraization.tex`, the section beginning
“Algebraization of formal sections” and `lemma-compare-with-derived-completion`
(Tag 0DXI), including the proof. Its coherent-sheaf statement specializes to the
restriction of tilde M. The node's seven-step proof, including the missing degree-zero
ML detail and arbitrary-open degree-zero extension, is transcribed in the theorem's
docstring. The ML detail uses the image of the surjective module-reduction tower,
not a false ML assertion for arbitrary towers of sections in degree zero.

Hypothesis and object correspondence:

- The commutative Noetherian local ring is `(A : Type u) [CommRing A]`
  with `[IsNoetherianRing A] [IsLocalRing A]`. `I : Ideal A` is arbitrary, with
  no completeness, properness or nonzero hypothesis on I.
- `U : (Spec (.of A)).Opens`, with `hU : forall x, x in U iff
  x.asIdeal != IsLocalRing.maximalIdeal A`, is precisely the punctured spectrum.
  This parametrization avoids choosing a second open with its own equality transports.
- `M : ModuleCat.{u} A` and `[Module.Finite A M]` represent every finite module.
  A finite A-module can always be represented in the universe of A; no independent
  index universe or restriction on ranks is imposed. All derived localization
  universes `wA`, `wT`, `wX` are explicitly bound, separately from u.
- The associated sheaf is Mathlib's `tilde.functor (.of A)`. We use
  `SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)`, with Mathlib's
  abelian instance and the project's shared category instance; we do not form a
  second derived category using Scheme.Modules' separate category instance.
- `sections A V` uses Mathlib's `modulesSpecToSheaf` followed by evaluation at V.
  Its A-action is exactly scalar transport through `Scheme.ΓSpecIso` and restriction.
  `derivedSections A V` applies its unbounded K-injective right derived functor to
  `tilde M[0]`. This is RΓ(V, tilde M restricted to V), computed from an ambient
  injective resolution. Open restriction of an injective module is injective,
  so ambient and intrinsic open derived sections agree.
- `cohomology A V i` is this derived functor followed by
  `DerivedCategory.homologyFunctor (ModuleCat A) i`. Thus every integer degree is
  allowed and negative sheaf cohomology is zero. No negative degree is silently
  replaced by degree zero or omitted.
- `reductions A I` sends M to the actual strict tower M/(I^(n+1) • top), with
  `Submodule.factorPow` transitions. Its map on f is `Submodule.mapQ f.hom`.
  The index n denotes the paper's positive exponent n+1; all nonadjacent transitions
  are retained. `reductionMap` is the actual quotient map from its concrete cone.
- T and c specify the universal total left derived functor of termwise
  `reductions A I`, localized at quasi-isomorphisms. This is the strict derived
  tensor tower: on a K-flat resolution with flat terms it is termwise
  P/(I^(n+1) P), canonically P tensor A/I^(n+1), with all transition maps.
  The binder `[T.IsLeftDerivedFunctor c ...]` is a model specification, not an
  assumption of the result or an arbitrary replacement tower. It applies to any
  universal derived pair, with no boundedness assumption.
- `completion A T` composes this tower with the actual unbounded right derived
  functor of ordinary inverse limit. It uses K-injective *tower* resolutions,
  not individually chosen triangulated cones. In modules products are exact;
  this is the universal derived-functor presentation of the mapping fibre of
  one minus shift on termwise products. `limitComparison` is built from the
  published right-derived unit and the Q/Qh comparison isomorphisms. It has no
  unspecified cone arrow or arbitrary isomorphism field.
- `η` is a natural completion unit. `hη` specifies its value on every complex:
  after the derived reduction comparison c it is `Q.map (ordinaryUnit A I P)`
  followed by the universal derived-limit comparison. `ordinaryUnit` is built
  by limit.lift of the quotient cone in every degree. This equation retains
  the actual reduction maps. On K-flat representatives c is invertible, so
  the equation fixes η; changing a cone map arbitrarily cannot satisfy it.
  Universal derived models and their normalized units may be supplied exactly
  as in the published ConstantCompletion interface. No object is selected from
  an unconstrained Nonempty existence theorem in this delivery.

Conclusion correspondence:

- A single family e is indexed by `V <= U`, integer i, and `i = 0 or V = U`.
  Therefore it gives all integer degrees on U and exactly degree zero on every
  open V. Its source is `(completedCohomology A T V i).obj M`, namely
  H^i(completion RΓ(V,tilde M)); its target is
  `limit (cohomologyTower A I V i M)`, namely the inverse limit of
  H^i(V,tilde(M/I^(n+1)M)). These are isomorphisms of A-modules, the natural
  coefficient structure on all groups in the node.
- The first conjunct fixes the canonical comparison. For each n it provides
  the unique derived arrow a from completed sections to reduced derived sections
  whose composite with η is `derivedSections.map (reductionMap ...)`.
  The equality `e.hom >> limit.π ... (op n) = homologyFunctor.map a` says e
  is induced by those reduction arrows. Uniqueness is asserted among *all*
  arrows satisfying the unit equation, not merely among chosen cones.
  The reduced target is derived complete since it is annihilated by a power
  of I; the completion reflection gives exactly this uniqueness.
- The last equality of that conjunct explicitly states that H^i(η), followed
  by e and its nth projection, equals the cohomology map induced by M to M/I^n M.
  At i=0 this is the required map on ordinary sections. The ordinary sections
  interpretation is the degree-zero right-derived comparison, not an arbitrary
  map out of an unrelated H^0 object.
- The second conjunct is naturality for every homomorphism of finite modules.
  On the inverse limit it uses `lim.map` of the actual reduction map of f,
  whiskered by the cohomology functor.
- The third conjunct is the open restriction square for every W <= V <= U.
  `derivedRestriction` is the right-derived natural transformation of actual
  presheaf restriction; `completedRestriction` applies completion and H^0 to it.
  `towerRestriction` is restriction on every reduction, and `lim.map` is its
  inverse-limit map. This is exactly the node's completed restriction square.
- Since e is one dependent family, the U,i=0 instance of the arbitrary-open
  clause is literally its U,i=0 instance of the all-degrees clause. Proof
  irrelevance identifies the two proofs of `i=0 or V=U`.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` and its ideals-FG
  characterization; `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`; HomologySequence supplies H^i.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec` and `Spec.map`.
- `Mathlib.AlgebraicGeometry.Modules.Tilde`: `tilde`, `tilde.functor`,
  `tilde.toOpen`, `tilde.toOpen_res`, `modulesSpecToSheaf`; their full source
  signatures/docstrings were read, including localization on basic opens.
- `Sheaf.Algebra.Homology.IdealPowerTorsionFunctor`: `ModuleCat.idealPowerTorsion`,
  imported for the node's contextual RΓ_K notation; no copy is introduced.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`: `IsDerivedLimit`
  and `IsDerivedLimitTriangle`, read with `scompile.py --source`; these express
  a Roos-triangle property, so they alone do not specify the functorial unit.
  The actual right-derived inverse limit is used instead.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`, its compatible
  quotient-family definition and `Submodule.factorPow`. Ordinary completion
  is not substituted for the derived completion of sections.
- `WeilConjectures.AlgebraicGeometry.PQFCohomology`:
  `sheafCohomologyAndHigherDirectImages`, read with `scompile.py --source`
  because the older local source lacks this published module. It identifies
  module cohomology with right derived sections and higher direct images.
- Published `Sheaf.Paper.CoefTowerCoaugmentation`:
  `WeilConjectures.CoefTower.moduleTowersKInjectives` and `moduleLimitAdditive`
  supply the ordinary module-tower infrastructure. Their owner
  `def-trf-coefficient-tower-operations` is a landed node and is added to
  stmt_deps as expressly authorized for landed statement dependencies. No
  compact-support or finite-field assumption enters those generic declarations.
- Proof-only imports are `RingedSpace.rgamma_derivedLimit`,
  `CategoryTheory.ringedPushforward_completion`, the ConstantCompletion
  equivalence and normalized quotient-completion interface, and
  `Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType`.
  The unstated proof dependencies (affine-support localization, coherent
  completion, punctured ML, ML acyclicity) have no modules to import; their
  source proof steps remain in the docstring for stage 3.

Searches made:

- msearch.py LeanFinder: “Cohomology of derived completion of sections on a
  punctured local spectrum equals inverse limit of quotient cohomology”. Eight
  results were localCohomology diagrams, ordinary completion and tilde results;
  none states the comparison.
- msearch.py LeanSearch: “Derived completion cohomology of coherent sheaves on
  a punctured spectrum is inverse limit of reductions”. Eight results concerned
  ordinary AdicCompletion and its module/ring structures; no comparison.
- msearch.py Loogle: `AdicCompletion, CategoryTheory.Sheaf`: zero hits.
- msearch.py Mathlib grep: `derived.*complet|complet.*cohomolog`: zero hits.
- rg in slopmaster2 WeilConjectures for the item id: no match. Searches for
  derived completion find the constant-sheaf/pro-etale reduction diagram and
  completeness predicate, which do not give ordinary punctured-spectrum sections.
- rg in lean/Sheaf for completion/cohomology/strict Roos: found the existing
  ConstantCompletion universal models, strictRoosComplex, open derived sections
  with abelian-group values, and ordinary-module tower instances. These were
  read. The new helper sections retain A-module values, whereas the existing
  openModuleSections and openModuleDerivedSections forget to abelian groups.
- rg for the new full theorem name in Mathlib, WeilConjectures and lean/Sheaf:
  no declaration collision. Other PuncturedCompletion files concern affine
  formal glueing, not this derived-cohomology comparison.

Edge cases checked mathematically before writing: A a field has empty U and
zero section complexes, so every displayed map is the unique zero-object map.
M=0 and V empty work the same way. For I=0, reductions are the constant M tower
and completion is the identity; for I=A, all positive reductions and completion
are zero. Every negative degree has zero reduced sheaf cohomology; the Milnor
argument also makes the completed source vanish. The theorem allows V=U and
W=V including identities, and allows every finite module map including zero.
No assumption that H^0(U,F) is finite, complete, or ML for an arbitrary tower
has been introduced. No statement is disputed.

Validation: the prescribed scompile.py compiled both its sandbox probe and the
actual library-name module cleanly (11.2 s and 10.9 s). There were no warnings.

## Second reading by NK

A separate reading pass reopened the original JSON and final Lean signature,
without changing the mathematical statement. The ring, ideal, punctured open,
finite module, associated sheaf, ordinary D(A), strict derived reductions and
normalized completion map match the objects listed above. The single e family
matches all integer degrees on U and H^0 on every V. Its coordinate equalities
match the reduction assertion, its homomorphism square matches naturality, and
its final square matches restriction. The same U,0 family component handles
both clauses. The negative-degree convention follows from derived sections
of tilde M[0]. The canonical-arrow uniqueness clause explicitly prevents an
existential family of unrelated cohomology isomorphisms from passing as the
canonical comparison.

This is the dispatched single worker's second pass; no other agent was started,
as explicitly required by the dispatch brief. It found and repaired two
implementation issues during compilation: the separate Scheme.Modules category
instance, and unnecessarily duplicated module-tower instances. The final file
uses the shared sheaf category and published generic tower instances. It also
replaced a quotient-map functor-law proof that caused a kernel timeout by the
existing `Submodule.factor_comp` theorem. No mathematical hypothesis or clause
was changed to resolve any of those errors.
