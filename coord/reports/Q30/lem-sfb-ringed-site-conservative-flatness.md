## Worker report

The module `Sheaf.Algebra.Category.ModuleCat.Sheaf.ConservativePointFlatness` states
`CategoryTheory.RingedSitePoint.isFlatOnSite_iff`, with its entire proof `sorry`.
Source read: Stacks Project, `sites-modules.tex`, Tag 05VC,
`lemma-check-flat-stalks`, lines 7350–7370. Its arbitrary-ring-sheaf criterion is
unchanged. The declaration docstring carries all four steps of the accepted DAG proof.

Hypothesis and clause correspondence:

- The size convention is represented by explicit universes `u v w t`,
  `{C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]`. The site is small
  relative to the coefficient universe after the convention's small-model replacement.
  Object and morphism universes remain independent. No equality of universes is imposed.
- The small site `(C,J)` is `{J : GrothendieckTopology C}` together with the category
  and relative smallness just listed. This also covers essentially small presentations.
- The arbitrary sheaf of commutative rings is `{R : Sheaf J CommRingCat.{w}}`.
- The sheaf of R-modules is `M : ringedSiteModules.{w}
  ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)`.
  The forgetful functor only changes the commutative ring's packaging.
- The set-indexed family is `{I : Type t}` and
  `p : I → GeometricMorphism (Type w) (Sheaf J (Type w))`.
  `GeometricMorphism` supplies inverse image, right adjoint, the adjunction, and
  preservation of finite limits. No member of the family is selected.
- Joint reflection on sheaves of sets is exactly
  `hp : JointlyReflectIsomorphisms (fun i : I ↦ (p i).inverse)`.
- The instruction to give inverse-image rings and modules their induced operations is
  `s : ∀ i : I, RingedSitePoint R (p i)`. These are normalized presentations, not
  arbitrary module functors: `ringUnderlying`, `moduleUnderlying`, `ringAdd`,
  `ringMul`, `ringZero`, `ringOne`, `moduleAdd`, `moduleZero`, and `moduleSMul`
  specify the finite-product transport and its naturality. The full structure signature
  and operation equations were read. `RingedSitePoint.nonempty` supplies such data
  for every point. The theorem applies to every presentation; it adds no restriction
  on the point or its ring/module inverse image, and chooses no unspecified object.
  The existing node `def-sfb-ringed-site-point`, already a proof dependency, is added
  to `stmt_deps` under the rule permitting added landed statement dependencies.
- Flatness of M is
  `SheafOfModules.IsFlatOnSite.{u, v, w, w} (J := J) (R := R) M`.
  This is the recorded exactness of the actual sheafified right tensor functor.
- The conclusion is an `↔`, with right-hand side
  `∀ i : I, Module.Flat (s i).ring ((s i).modules.obj M)`.
  Here `(s i).ring` is R_i and `(s i).modules.obj M` is M_i, identified with
  the prescribed inverse images by the normalized presentation.
- There is no constant-ring, quasi-coherence, finite generation, finite presentation,
  nonzero-ring, nonempty-family, or boundedness assumption.

Recorded dependency interfaces read and used:

- `def-weil-size-convention`: the record says this is a metatheoretic convention;
  it has no declaration to import. Explicit universes and relative smallness implement it.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  the transparent abbreviation for Mathlib `SheafOfModules` and its linear morphisms.
- `Sheaf.CategoryTheory.Sites.GeometricMorphism`,
  `CategoryTheory.GeometricMorphism`: full structure and docstring read.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`,
  `SheafOfModules.IsFlatOnSite`: exactness of `siteSheafTensorRight`.
- `Mathlib.RingTheory.Flat.Basic`, `Module.Flat`: the record's module-flatness clause;
  the arbitrary-injective-map characterization was also read. The record's primary
  `RingHom.Flat` is the ring-map clause and is not needed for this module-only conclusion.
- `Sheaf.CategoryTheory.Sites.RingedSitePoint`,
  `CategoryTheory.RingedSitePoint` and `.nonempty`: normalized inverse-image operations.
- `Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly`,
  `CategoryTheory.JointlyReflectIsomorphisms`: its `isIso` clause is precisely conservativity.
- `Sheaf.Algebra.Homology.KFlatCoefficientUniverse`: the already established
  `SheafOfModules.hasSheafify_coefficientUniverse` and
  `.wEqualsLocallyBijective_coefficientUniverse` instances supply the infrastructure
  of `IsFlatOnSite` for independent site and coefficient universes. No new instance
  or helper definition is introduced.

Proof imports (plain imports, in addition to the public statement imports) match the
recorded plan: `RingedSitePointFlat` (`RingedSitePoint.flat`),
`RingedSitePointExact` (`RingedSitePoint.exact`), `RingedSitePointTensor`
(`RingedSitePoint.tensor`), `CochainTensorUniverses`
(`SheafOfModules.cochainModulesMonoidal` and the localization tensor instances),
and `Mathlib.Algebra.Homology.BifunctorShift` (`CochainComplex.mapBifunctor`).
`Module.Flat.rTensor_exact` and `.lTensor_exact`, and the three-term complex
interface, are supplied by these imports and `Mathlib.RingTheory.Flat.Basic`.
No already stated proof dependency is omitted.

Edge cases checked mathematically before writing:

- Empty family: the right side is vacuous, but joint reflection then forces every
  set-sheaf arrow to be invertible. Applied to the underlying homology-to-zero map,
  the same argument proves every relevant tensor complex exact. No `Nonempty I` is needed.
- Zero module and zero ring: both are allowed by the bundled structures, and give
  the expected flatness. The right side uses ordinary flatness, including the zero module.
- Empty/degenerate site: no object or point is selected, and the same conservative
  zero-detection argument applies.
- Arbitrary varying R and arbitrary M: all types and operations depend on R;
  the code imposes no constant or quasi-coherent presentation.
- Independent category object/morphism universes and arbitrary index universe:
  the relative smallness API works without collapsing them.

Searches actually run:

1. `msearch.py ... leansearch` query
   `Flatness of a module sheaf is detected at a conservative family of points over the stalk rings`:
   eight hits, including `Module.flat_of_isLocalized_span`,
   `AlgebraicGeometry.Flat.iff_flat_stalkMap`, and ordinary module localization lemmas;
   no arbitrary-ring-sheaf criterion.
2. `msearch.py ... leanfinder` query
   `A sheaf of modules over an arbitrary sheaf of commutative rings is flat if and only if its stalk modules at a conservative family of topos points are flat`:
   eight hits, including scheme stalk-map criteria, `RingHom.Flat.propertyIsLocal`,
   and ordinary module flatness/localization; none states this item.
3. `msearch.py ... loogle` query `SheafOfModules, Module.Flat`: zero hits.
4. `msearch.py ... grep` query
   `flat.*stalk|stalk.*flat|IsFlatOnSite|jointly.*[Rr]eflect`, directory `CategoryTheory`:
   25 hits, mainly the joint-isomorphism-reflection API; no flatness criterion.
5. Direct `rg` searches with these patterns in `lean/WeilConjectures` and
   `lean/Sheaf`, and the exact node-id `grep -rn` in `lean/WeilConjectures`:
   no exact item. The ringed-space stalk results and constant-coefficient étale
   flatness results specialize different objects. The general ringed-site
   K-flat-stalk criterion concerns complexes, not the flat module predicate.
   Relevant existing general-site modules were opened, including
   `RingedSitePointAcyclic` and `RingedSiteKFlatStalkCriterion`.
6. `rg` for `isFlatOnSite_iff` in the proposed namespace's source areas and
   `dag/lean_names_upstream.json`: only the distinct local equational criterion
   appeared. The full proposed declaration name has no existing declaration.

No new nodes, dependency modules, statement correction, or disputed statement.
Only `lean` and the permitted added landed statement dependency change in the item.
The server's `scompile.py` compiled both sandbox and library module names cleanly
(1.7 s and 1.6 s), without errors or unexpected warnings.

## Second reading by Q30

A separate pass reread the original node, source lemma, dependency interfaces, and
complete generated declaration. This pass was performed within the dispatcher worker;
the brief explicitly prohibits starting another agent. The maintainer's independent
review remains the independent review of this delivery.

The second pass matched the site and relative smallness binders to the universe
convention, arbitrary R to `Sheaf J CommRingCat`, M to the recorded general-site
module category, each p to the recorded geometric-morphism datum, and conservativity
exactly to joint reflection on set sheaves. It checked every normalized operation
field against the node's finite-product-transport clause: s supplies a presentation
of the prescribed operations, rather than an unrelated scalar action. The existence
result means the presentation binder excludes no point. Both sides of the iff use
the recorded flatness predicates over exactly R and the induced stalk rings.
The empty index and zero-module cases remain present, and no finite-presentation or
quasi-coherence hypothesis slipped in. The extra statement dependency names the
already landed normalized presentation notion used in the signature. No mismatch was
found and no statement change was required. The only postponed proof is the theorem
of the assigned node; no definitions or supporting theorems were added.
