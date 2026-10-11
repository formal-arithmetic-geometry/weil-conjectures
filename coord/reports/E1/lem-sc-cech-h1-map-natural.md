## Worker report

The module `Sheaf.AlgebraicGeometry.CechH1MapNatural` states
`AlgebraicGeometry.Scheme.Modules.cechH1Map_natural`, with one `sorry` proof and no
new definition. It asserts existence of the canonical first Čech comparison for
all coefficient modules, together with naturality. The statement of the node is
unchanged. Its `stmt_deps` gains the already-landed
`def-sc-module-cech-comparison`, permitted by coord/brief-stage2.md §5,
STMT_DEPS MAY GAIN LANDED NODES. No new node or dependency module is needed.

Hypothesis and clause correspondence:

- X is a scheme: `(X : Scheme.{u})`, the recorded Mathlib scheme structure.
- An open covering: `(U : ι → X.Opens)` and `(hcover : iSup U = ⊤)`.
  Opens are not assumed affine, distinct, nonempty, or finitely many.
- Every O_X-module H: `∀ F : X.Modules` in the type of the existential family `c`.
  `X.Modules` is the recorded `SheafOfModules.{u} X.ringCatSheaf` category.
  It agrees definitionally with the moduleRings carrier used by module cohomology.
- The source is first Čech cohomology:
  `((cechComplexFunctor U).obj F.presheafModuleCat).homology 1`.
  `presheafModuleCat` has the original section groups and restriction maps;
  restriction of scalars gives each group its Γ(X,O_X)-module structure.
  Mathlib's complex uses all ordered pairs, including repeats, and the alternating
  restriction differential. This is the open-site specialization of
  def-weil-pbc-site-cech-complex; no separate Čech definition is introduced.
- The target is H^1(X,H):
  `(RingedSpace.moduleCohomology X.toRingedSpace 1).obj F`, as pqf-def-cohomology
  specifies. It is module cohomology, not abelian-sheaf Ext cohomology.
- There is a canonical homomorphism: `∃ c`, with
  `∀ F, IsModuleCechComparison U F 1 (c F)`. This predicate requires the comparison
  equation with alpha, beta and the resolution identification for EVERY injective
  resolution. Thus the existential is constrained to the canonical comparison,
  not just an arbitrary natural family such as zero. Morphisms in ModuleCat are
  homomorphisms of the underlying additive groups and have precisely the scalar
  linearity of the source's comparison (01EQ is valued in D^+(O_X(X))).
- Every coefficient morphism: `∀ (F F' : X.Modules) (φ : F ⟶ F')`.
- The induced cochain map applies φ to each section: the map of
  `PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op` on `φ.val`,
  followed by `cechComplexFunctor U`. Its degree components apply the module
  morphism to each product factor. `HomologicalComplex.homologyMap ... 1`
  takes the resulting map on first cohomology.
- The induced map followed by c_H' equals c_H followed by H^1(X,φ): exactly
  `HomologicalComplex.homologyMap ... 1 ≫ c F' =
   c F ≫ (RingedSpace.moduleCohomology X.toRingedSpace 1).map φ`.

Declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`.
- Mathlib.AlgebraicGeometry.Modules.Sheaf: `Scheme.Modules` and its category.
- WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf:
  `Scheme.Modules.presheafModuleCat` (the sectionwise scalar restriction).
- Mathlib.Algebra.Category.ModuleCat.Presheaf:
  `PresheafOfModules.forgetToPresheafModuleCat` (including its map definition).
- Mathlib.CategoryTheory.Sites.SheafCohomology.Cech:
  `CategoryTheory.cechComplexFunctor`, the existing specialized Čech complex.
- Sheaf.Paper.PQFCohomology: the recorded
  `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages` identifies its degree
  functors as `RingedSpace.moduleCohomology`. Its full signature/docstring read.
- Sheaf.Topology.RingedSpaceModuleCohomology:
  `RingedSpace.moduleCohomology`, right-derived module-valued global sections.
- Sheaf.CategoryTheory.SiteCechComplex: `SiteCechComplex`, `complexFunctor`,
  `cochainsMap` and `cohomologyFunctor` read; these record the general-site notion.
  The landed canonical-comparison module uses Mathlib's open-site specialization
  with module coefficients, so the generic choice binder is unnecessary here.
- Sheaf.AlgebraicGeometry.ModuleCechComparison:
  `Scheme.Modules.IsModuleCechComparison`; its full defining equation and the
  definitions of `moduleCechDouble`, `moduleCechAlpha`, `moduleCechBeta` were read.
  The only import is this module, which supplies every identifier required.

Edge cases checked: zero module; an empty scheme and empty index type (the cover
condition is then allowed); a one-open cover; repeated or empty opens; infinite
covers. No Nonempty or finiteness binder is imposed. The common universe u is the
ambient universe containing both the scheme and its set of cover indices, as in
its landed canonical-comparison definition. All universes and variables are
explicit; auto-bound implicits are not used. No characteristic assumptions occur.

Source read: https://stacks.math.columbia.edu/tag/01EQ, including the full proof.
Local literature sources are absent on this clone. The source constructs the
comparison as beta followed by inverse alpha, naturally in O_X-modules; the
landed characterization is precisely this equation for every resolution.
The docstring expands all four proof steps of the item's node with their DAG
references; this stage leaves the proof as `sorry`.

Searches:

- msearch.py leanfinder: "The canonical map from Cech cohomology of an open cover
  to sheaf cohomology is natural in the sheaf of modules": eight global-section
  naturality hits, none the comparison statement.
- msearch.py loogle: "cechComplexFunctor, homologyFunctor": zero hits, service
  reports unknown identifier cechComplexFunctor.
- msearch.py grep: "cech.*(cohom|natural)|cohom.*cech": LocalCohomology and
  Sites/SheafCohomology/Cech, neither supplies the canonical comparison map.
- rg of WeilConjectures for Cech/cohomology/naturality: existing complexes and
  comparison isomorphisms for acyclic classes, not this theorem for all modules.
- rg of lean/Sheaf for canonical comparisons found the landed
  ModuleCechComparison definition and AffineModuleCechComparisonNatural theorem.
  The latter requires quasi-coherence and affine intersections and does not state
  this item. The general comparison-map-naturality DAG node has no Lean record.
- rg of WeilConjectures for the item's exact id: no hit. Search of
  dag/lean_names_upstream.json for IsModuleCechComparison/moduleCechComparison:
  no upstream declaration with these names.

Validation: lcompile.py compiled the final module cleanly (2.2 seconds).
No STATEMENT-DISPUTED flag and no mathematical correction is necessary.

## Second reading by E1

I reread the node, its Stacks source (Cohomology, Lemma 01EQ), and
`Sheaf.AlgebraicGeometry.CechH1MapNatural`. The correspondence is exact:

- The scheme is `(X : Scheme.{u})`; the common universe and explicit `ι : Type u`
  cover the node's scheme and index family.
- The open covering is `(U : ι → X.Opens)` with `hcover : iSup U = ⊤`.
  No finiteness, nonemptiness, affine, or separation assumption is added.
- An arbitrary `O_X`-module is `F : X.Modules` under the existential family
  `c : ∀ F, ...`; its source is `(cechComplexFunctor U).obj F.presheafModuleCat`
  and its target is `(RingedSpace.moduleCohomology X.toRingedSpace 1).obj F`.
- Canonicality is rendered by `IsModuleCechComparison U F 1 (c F)`, which
  quantifies over every injective resolution, using the landed dependency
  `def-sc-module-cech-comparison`.
- For every `F F'` and `φ : F ⟶ F'`, the displayed equation uses the Cech map
  induced by `φ.val` and `HomologicalComplex.homologyMap ... 1`, followed by
  `c F'`, and equals `c F` followed by the module-cohomology map. Composition
  order and quantifiers agree with the node.

Edge cases checked are zero modules, one-open covers, repeated or empty opens,
empty index types (when the cover equation permits them), infinite covers, and
the empty scheme. No characteristic or `n = 0` hypothesis is present; this is
the fixed degree-one case. The module compiled with `lcompile.py` without
errors or warnings. Searches of Mathlib, the upstream source, and `lean/Sheaf`
found no existing theorem with this statement; the affine/quasi-coherent
comparison theorem is a different result. The only change recorded by this
second reading is the explicit dependency on the landed canonicality predicate;
the Lean statement itself required no repair.
