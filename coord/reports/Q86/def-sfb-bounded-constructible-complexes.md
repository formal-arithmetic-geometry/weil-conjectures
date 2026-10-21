## Worker report

Existing-definition delivery for def-sfb-bounded-constructible-complexes. No Lean module is
written: the exact existing declarations are
`AlgebraicGeometry.ProEtale.boundedConstructible` and
`AlgebraicGeometry.ProEtale.BoundedConstructible`, in
`WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory` (lines 62 and 87).
Read the whole module and its imported constructibility definition, then confirmed the
current live source using `scompile.py --source` on that module. Only the item's `lean`
field changes; no theorem, definition, new node, or dependency repair is introduced.

The source is the current blueprint
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/` followed by
`sk-def-sfb-bounded-constructible/def-sfb-bounded-constructible-complexes.md`, order 1642.
The node's stage-1 clarification specifies the general internal-module predicate rather
than the scalar-local-model predicate. The upstream definition uses precisely that
clarified predicate.

Hypothesis and clause correspondence:

- Coefficient category: the upstream section binds `{A : Type u'}`,
  `[Category.{u + 1} A]`, `[Abelian A]`, `[IsGrothendieckAbelian.{u + 1} A]`,
  `[MonoidalCategory A]`, `[MonoidalPreadditive A]`, `[SymmetricCategory A]`, and
  `[MonoidalClosed A]`. These are exactly the Grothendieck abelian, closed symmetric
  monoidal, additive-tensor assumptions. The coefficient object universe `u'` is
  independent of the scheme universe `u`. The Hom universe `u+1` is the size of the
  small-site model used by these recorded dependencies; no equality of site object
  and site morphism universes is imposed.
- Scheme and small pro-etale site: `{X : Scheme.{u}}` and
  `Scheme.ProEt.topology X` use the recorded Mathlib site of weakly etale objects.
- Sheaf tensor: `Sheaf (Scheme.ProEt.topology X) A` carries
  `CategoryTheory.Sheaf.monoidalCategory`, the sheafified objectwise coefficient
  tensor. The recorded `sfbSheafTensorStructure` explicitly uses that same monoidal
  instance, not another tensor. Its comparison and properties give the tensor and
  unit descriptions of the dependency.
- Ring and commutativity: `(R : Sheaf (Scheme.ProEt.topology X) A) [MonObj R]`
  expresses the ring object; `[IsCommMonObj R]` is in the source section context.
  Neither definition's body needs commutativity, so Lean omits this unused instance
  from the elaborated definition parameters. Specializing this general definition
  to the node's commutative R gives exactly the requested objects; no extra choice
  of multiplication or action is introduced.
- Left modules: `Mod (Sheaf (Scheme.ProEt.topology X) A) R` is the recorded Mathlib
  category. `ModObj` gives the unital associative action, and `Mod.Hom` the
  compatible morphisms.
- Ordinary unbounded derived category: the ambient type is
  `DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R)`, the localization of
  integer cochain complexes at quasi-isomorphisms. The imported module-object
  instances provide its abelian and localization interfaces. Neither a bounded
  complex category nor a completion replaces this ambient category.
- Boundedness: the first factor of `boundedConstructible R` is
  `DerivedCategory.TStructure.t.bounded`. Mathlib defines this as `t.plus ⊓ t.minus`,
  i.e. existence of lower and upper integer t-structure bounds. The existing
  `mem_boundedConstructible_iff` in the same module identifies it with
  `∃ a b : ℤ, ∀ i : ℤ, (i < a ∨ b < i) → IsZero (H^i K)`.
  The characterization does not explicitly require `a ≤ b`; this is equivalent
  to the node's ordered witnesses by taking `min a b` and `max a b`. Outside that
  enlarged interval one is outside the original interval. The reverse implication
  forgets the inequality. This also covers all-zero cohomology.
- Every integer cohomology module is constructible: the second factor is exactly
  `fun K ↦ ∀ n : ℤ, IsConstructibleModuleObject R
    ((DerivedCategory.homologyFunctor _ n).obj K)`.
  The recorded predicate expands to `∃ S : Scheme.Stratification X, ∀ a : Fin S.n,
  IsLocallyFinitelyPresented ((ProEtale.upperStar A (S.immersion a)).obj R)
    (((ProEtale.upperStar A (S.immersion a)).mapMod R).obj M)`.
  This is finite stratification, pullback of the actual ring and actual module,
  and local finite presentation on every stratum. Its imported local-presentation
  definition uses finite-free presentation maps, with no scalar-matrix restriction.
- The category is exactly `(boundedConstructible R).FullSubcategory`, by the
  `BoundedConstructible` abbreviation. Mathlib's `ObjectProperty.FullSubcategory`
  uses the induced category on the object projection, so morphisms, identities,
  and composition are the ambient derived ones.
- No derived completeness predicate occurs in either body. There is no
  Noetherian hypothesis on these definitions. Triangulatedness is a separate
  downstream assertion, not part of this definition delivery.

Dependency declarations read and used by the existing construction:

| Node | Module | Declaration / interface |
| --- | --- | --- |
| def-weil-pbc-proetale-site | Mathlib.AlgebraicGeometry.Sites.Proetale | AlgebraicGeometry.Scheme.ProEt; Scheme.ProEt.topology |
| sk-def-sfb-sheaf-tensor | Sheaf.CategoryTheory.SheafTensor | CategoryTheory.sfbSheafTensor_properties; sfbSheafTensor_comparison; sfbSheafTensorStructure |
| sk-def-sfb-ring-object | WeilConjectures.CategoryTheory.RingObjects.RingPresheaf | CategoryTheory.MonObj; CategoryTheory.IsCommMonObj (the generic interfaces exported by the recorded module) |
| sk-def-sfb-module-objects | Mathlib.CategoryTheory.Monoidal.Mod | CategoryTheory.Mod; ModObj; Mod.Hom |
| def-weil-abstract-derived-category | Mathlib.Algebra.Homology.DerivedCategory.Basic | DerivedCategory; HasDerivedCategory; DerivedCategory.Q |
| sk-def-sfb-derived-categories | Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions | The node records the unbounded DerivedCategory convention and explicitly identifies this same upstream bounded-constructible category in its note; no derived functor is needed to define this predicate |
| def-sfb-constructible-module | WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def | AlgebraicGeometry.ProEtale.IsConstructibleModuleObject |

Also read `DerivedCategory.homologyFunctor` and its localization-factorization
signature in Mathlib's HomologySequence module; the canonical bounds in
Triangulated.TStructure.Basic; the FullSubcategory structure/category; and the
module-object derived-category source. Existing sources already import the
interfaces their bodies need; an existing binding creates no new import module.

Edge cases checked directly against the bodies: zero cohomology admits bounds
`a=b=0`; unordered witnesses still give ordered witnesses as above; a complex
concentrated in one degree is allowed; unbounded nonzero cohomology fails the
first factor even if every cohomology object is constructible. Empty schemes
and zero ring objects are not excluded. Constructibility quantifies over all
integers and allows a separate stratification for each cohomology module; no
common stratification or lissity is silently required. An empty stratification
has a vacuous per-stratum condition as in the dependency's definition. The
category contains every ambient morphism between qualifying objects.

Searches (all via prescribed msearch.py, Q86 and this item):

- leanfinder query `bounded constructible derived complexes of internal module
  sheaves over a ring object with constructible cohomology`: eight results,
  including LightCondMod, CondensedMod, and SheafOfModules.isFinitePresentation;
  no exact Mathlib definition of this predicate.
- loogle query `DerivedCategory, IsConstructible`: zero hits; unknown identifier
  `IsConstructible` in Mathlib.
- grep query `boundedConstructible|BoundedConstructible|IsConstructibleModuleObject`:
  zero Mathlib hits.
- `rg` of these names in the prescribed `lean/WeilConjectures` and `lean/Sheaf`
  trees found the exact upstream ProEtaleModule/DerivedCategory definitions and
  their many consumers. Narrow declaration search confirmed their locations.
- Source-id search in `lean/WeilConjectures` found no literal node-id docstring;
  this does not change the name/body match.
- Read `Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible`: it imports the
  same definitions unchanged and adds only a separate triangulatedness theorem
  under weak Serre conditions. It is not a competing definition.

No statement dispute or node fault remains. There is no repair note for this item.

## Second reading by Q86

Performed a separate rereading of the node, complete live upstream module, and
constructibility definition. No second agent was started, as the dispatcher brief
explicitly forbids that. This is a worker self-check; independent review belongs
to the maintainer as specified in the task.

The first conjunct is canonical boundedness, not derived completeness; the second
is the recorded general `IsConstructibleModuleObject` for every integer cohomology
module, not the separate scalar-local-model predicate. The category abbreviation
uses FullSubcategory and hence imposes no restriction on morphisms. All coefficient
and ring hypotheses correspond as detailed above. The apparently missing ordered
bound clause is redundant by min/max and requires no source or node change. The
unused commutativity assumption likewise only generalizes the existing definition;
its commutative specialization is exactly the node. No hypotheses, clauses, or
objects need repair. Both requested declarations are listed in `lean.declarations`;
the primary definition signature is copied verbatim from the live source. No
new definition is needed, and no Lean file is included.

## Delivery validation

On this retry, the first two prescribed dry runs failed because upstream published
object files were missing: KanExtension.Preserves and GrothendieckCategory.Subobject,
then Topology.Stratification. All three sources were confirmed available using
`scompile.py --source`; no source, launcher tool, or published artifact was changed.
The next `deliver2.py Q86 def-sfb-bounded-constructible-complexes --no-push` passed
preflight and compilation, producing dry-run commit `a58463241b5` (not pushed).
The compile wrapper successfully checked the existing-definition import on the server.

Rechecked the current shared node against the retained sandbox: only `lean` differs.
Reread every current statement-dependency record and the current blueprint source;
the existing binding and clause correspondence above remain unchanged.
