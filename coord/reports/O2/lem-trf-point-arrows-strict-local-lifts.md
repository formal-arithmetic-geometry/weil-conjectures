## Worker report

The module `Sheaf.TraceFormula.PointArrowsStrictLocalLifts` states
`AlgebraicGeometry.Scheme.point_arrows_strict_local_lifts`, with its entire proof
`sorry`. Its three helper definitions contain real canonical data: the geometric
point morphism assembled from Mathlib's stalk/skyscraper adjunction, the chosen
small affine representative, and the spectrum-of-colimit-injection projection.
Every helper belongs to the geometric point/strict-localization notions already
in this node, rather than introducing an independent notion.

Hypothesis and clause correspondence:

- The scheme is `{S : Scheme.{u}}`. Both fields are independently named
  `{Ωt Ωs : Type u}`, each with `[Field] [IsAlgClosed]`. The maps `t` and `s`
  are precisely the two maps from their spectra. This is the project size
  convention: one arbitrary ambient universe, without any equality of fields
  or extension/algebraicity assumption.
- `strictHenselizationScheme s` and `strictHenselizationStructuralMap s` are
  the recorded inverse-limit strict localization and its canonical map `rho`.
- The left side of `Θ` is exactly the subtype of scheme maps `a` with
  `a ≫ strictHenselizationStructuralMap s = t`. The right side is natural
  transformations between the two canonical direct-image functors, from `t`
  to `s`, as specified by `GeometricMorphism`.
- The `≃` asserts a bijection. Its first characterization is quantified over
  every lift `a`, set sheaf `F`, etale `U`, geometric lift `u`, and section `z`.
  `GeometricMorphism.inverseMate (Θ a)` has direction `F_s → F_t`.
  The input and output are the recorded `pointedEtaleGerm` injections, hence
  exactly the germs of the node, not a replacement stalk construction.
- The formula is written after EVERY pointed affine representative refinement
  `f : (strictLocalLiftRepresentative s j).1 ⟶ U`. The equation
  `(pointSmallEtale s).fiber.map f (...) = u` says it refines `(U,u)`.
  The canonical map `c_(U,u)` is `strictLocalLiftProjection s j ≫ f.left`.
  This is the same projection for every such refinement, by the limit cone
  relations and cofilteredness. Representatives cover all affine pointed
  objects, and affine pointed objects refine every `(U,u)`. Consequently this
  formulation covers every germ on arbitrary, including nonaffine, `U`.
  The existential `v` packages the over-S equation without an auxiliary
  postponed theorem: its scheme map is REQUIRED to equal that composite with
  `a`, and its germ has the prescribed value. Such `v` is unique by its map.
- For EVERY `τ : Ωt ≃+* Ωt` the sole condition is
  `Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ t = t`.
  `r : Aut (etaleGeometricPointMorphism t).direct` is a point automorphism.
  Its mate is specified on every germ, with `v'.left` required to equal
  `Spec τ ≫ v.left`. Thus `r` is specifically the change-of-lifts automorphism.
- The SAME `r` and `Θ` satisfy the final equation for every `a`.
  The existential subtype `a'` is uniquely specified by
  `a'.val = Spec τ ≫ a.val`, and `Θ a' = r.hom ≫ Θ a` is precisely
  `Θ(a ∘ Spec τ) = Θ(a) ∘ r_τ` in Lean's left-to-right composition convention.
  No `let`/hidden proof binder is used in any public signature.
- No normality, Noetherianity, finite type, support specialization, or algebraic
  extension is assumed anywhere. There is no restriction to generic points.

The germ characterization determines `Θ` uniquely: all germs are covered by
pointed affine refinements, so it determines the natural transformation on
inverse images; adjunction mates determine the direct-image arrow. Hence the
existential equivalence is canonical, rather than an arbitrary bijection. The
same argument determines `r` from its germ formula.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; geometric points are
  the node's inline field/maps encoding. Read `Scheme.SpecToEquivOfField` in
  `Mathlib.AlgebraicGeometry.ResidueField` for the equivalent residue data.
- `WeilConjectures.AlgebraicGeometry.StrictHenselization`:
  `strictHenselizationRing`, `strictHenselizationScheme`,
  `strictHenselizationCone`, `strictHenselization_properties`, the representative
  functor and its equivalence. The recorded declaration names are retained;
  the upstream module is selected under the explicit duplicate-import rule.
- `WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap`:
  `strictHenselizationStructuralMap`, `exists_strictHenselizationStructuralMap`.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`, `Etale`.
- `Sheaf.CategoryTheory.Sites.GeometricMorphism`: `GeometricMorphism`,
  `GeometricMorphism.inverseMate`, with the exact direct-image orientation.
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`: `pointedEtaleGerm`,
  `pointedEtaleStalkDiagram`, `pointedEtaleStalk`. Mathlib's `sheafFiber` uses
  definitionally the same colimit, as confirmed by successful type checking.
- Proof imports: `Mathlib.CategoryTheory.Sites.Point.Skyscraper` supplies the
  sheafification-stalk isomorphism, `Mathlib.CategoryTheory.Yoneda` the Yoneda
  bijection, and `WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization`
  the recorded affine initiality result. Their source declarations and full
  docstrings were read. Stalk-representable and cofilteredness dependencies are
  Mathlib leaves in the respective point Basic and EtalePoint modules.

Source check: read the full specialization construction in the local
`literature/stacks-project/etale-cohomology.tex`, section-specialization, including
its final direct-image 2-morphism interpretation. It specifies the germ formula.
The node explicitly supplies its own converse and equivariance; all six proof
steps are retained in the theorem docstring.

Edge cases checked: unrelated supports may give two empty hom/lift sets, and the
statement imposes no nonemptiness. Equal points and identity field automorphisms
are included. The two fields may be different and arbitrarily transcendental
algebraically closed extensions. No support specialization is added. Nonaffine
`U` is included by the universally quantified pointed refinement, without assuming
unique refinements. All set-valued sheaves in the standard `Type (u+1)` convention
are included. The empty scheme has no given geometric points, so that case is
correctly vacuous. Source/target morphism universes stay `u`; no site/coefficient
universe equality was imposed.

Searches (all through the prescribed tools/read-only sources):

- msearch LeanFinder: "Morphisms of points of the small etale topos correspond
  to geometric lifts into the strict henselization". Eight hits, mainly
  `Scheme.Etale.forget`/fully faithful and standard-etale ring presentations;
  no lift/point-arrow classification.
- msearch Loogle: `"Point.Hom", "strictHenselization"`: zero hits.
- msearch grep: `strictHensel.*(Hom|hom|point)|Point.*strictHensel`, subdirectory
  `AlgebraicGeometry`: zero hits.
- msearch LeanSearch: "Natural transformations between geometric stalk functors
  correspond to lifts into a strict localization". Eight hits on category
  localization natural transformations and topological stalk-map naturality;
  none states this result.
- `rg` in upstream WeilConjectures and `lean/Sheaf` for this node id and
  strict-local lift/point-arrow phrases: the normal-generic transitivity
  consumer mentions this input, but does not provide it. Its direct-image
  orientation and `Type (u+1)` convention agree with this delivery.
- Exact-name `rg` over Mathlib, upstream, `lean/Sheaf` and
  `dag/lean_names_upstream.json` found no existing declaration for any of the
  four names introduced in this module.
- Current upstream dependency sources absent in the older local checkout were
  read with `scompile.py --source`, including the strict-local ring colimit,
  structural morphism, and affine initiality source modules.

No statement correction, new node, or STATEMENT-DISPUTED flag is needed.

Import selection: the structural-map dependency already imports
`WeilConjectures.AlgebraicGeometry.StrictHenselization`, which supplies precisely
the declarations named in the limit node's lean record. Its historical
`Sheaf.AlgebraicGeometry.StrictHenselization` module duplicates these declarations
using a different presentation of the same canonical construction. As explicitly
authorized by the brief's duplicate-import repair instruction, this delivery
imports only the upstream owner of the recorded declarations. No mathematical
interface is generalized or redefined, so no dependency module or record repair
is necessary. The projection is exactly the expression in the recorded
`exists_strictHenselizationStructuralMap` characterization.

An attempted lean-only rebind of that dependency's module was removed as
unnecessary: preflight validates the dependency's inherited proof steps against
its proof_deps and found five existing missing-proof-dependency errors. Those
errors are reported here rather than editing unauthorized dependency fields.
The actual Lean statement uses the existing recorded full declaration names.

## Second reading by N2

Author's self-check under the dispatcher brief; an independent reading remains
with the maintainer, as explicitly required by the task. No second agent was
started. Reopened the node and final Lean statement, matched every hypothesis
and clause as above, and checked both composition directions. The germ formula
includes arbitrary `U` via every affine representative refinement, and the
field-automorphism formula uses precisely the same `r` as the equivariance
identity. The subtype witnesses cannot introduce arbitrary maps because their
underlying morphisms are explicitly fixed. The upstream import selects the existing recorded declaration names without
redefining their notions. A compile failure
for left exactness was diagnosed as the missing smaller-size AB5 instance for
`Type (u+1)` and repaired by Mathlib's universe transport, retaining the full
site and coefficient universes. No mathematical hypothesis was changed.

Validation: the final module compiled cleanly through scompile.py in both the
sandbox and library-position checks (5.0 s / 3.2 s), with no warnings.
