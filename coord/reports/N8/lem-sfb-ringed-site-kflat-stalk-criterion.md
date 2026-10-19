## Worker report

The delivery states `CochainComplex.ringedSite_kFlat_stalk_criterion`, the two
clauses of Stacks 0DEN, and supplies the missing ordinary-module inverse-image
presentation `CategoryTheory.RingedSitePoint`. The item's natural statement,
proof, proof dependencies and all review metadata are unchanged. Only its Lean
record and the added definition dependency change. Q63's 03:26 stage-1 merge
reviewed its proof split; it did not supply a Lean record or review Lean. Thus
the preceding worker's stale-stage-1-assignment diagnosis does not apply to
this stage-2 statement task.

Hypotheses and clauses of the item, individually:

- A site small in the coefficient universe is `{C : Type u} [Category.{v} C]
  [EssentiallySmall.{w} C] (J : Precoverage C) (hJ : J.IsSiteForCoverings)`.
  Sheaves use `J.toGrothendieck`. The site, its morphisms and coefficients retain
  independent universes; essential smallness expresses precisely the stated
  relative-smallness convention. No finite limits of C are assumed.
- The commutative ring sheaf is `R : Sheaf J.toGrothendieck CommRingCat.{w}`.
- The unbounded complex is `K : CochainComplex (ringedSiteModules.{w}
  ((sheafCompose J.toGrothendieck (forget₂ CommRingCat RingCat)).obj R)) ℤ`.
  These are the recorded ordinary sheaves of R-modules, with integer cochain grading.
- Each point is `p : GeometricMorphism (Type w)
  (Sheaf J.toGrothendieck (Type w))`, the recorded adjunction with finite-limit
  preserving inverse image. This does not restrict points to those represented
  by an underlying topological space or a particular site functor.
- `s : RingedSitePoint R p` is an explicit presentation of the induced stalk
  ring and module inverse-image functor. `s.ringUnderlying` identifies the ring
  carrier with `p.inverse.obj |R|`. Its four graph equations prescribe addition,
  multiplication, zero and one. `s.moduleUnderlying` is natural and identifies
  each carrier and map with the inverse image of its underlying set sheaf.
  The three module graph equations prescribe addition, zero and the scalar
  action; the scalar graph uses the SAME `s.ringUnderlying`. Universal tests
  T include the sheaf products of operands and terminal sheaf. Consequently
  these equations mean exactly inverse-image finite-product transport. No
  unspecified action, arbitrary map, or choice of scalar structures is used.
- K-flatness on the source is the dependency's recorded
  `CochainComplex.IsKFlatIndependentCoefficients (R := R) K`.
- The first conjunct universally quantifies p and its normalized presentation s.
  Given source K-flatness it concludes
  `(HomologicalComplex.quasiIso (ModuleCat s.ring) (.up ℤ)).kFlat
  ((s.modules.mapHomologicalComplex (.up ℤ)).obj K)`.
  This is the recorded ordinary-module K-flat predicate, and the complex is
  termwise inverse image on its objects AND differentials.
- The converse quantifies `(I : Type t)`, an arbitrary family p, and a normalized
  presentation `s i` at each point. Its conservativity hypothesis is exactly
  `JointlyReflectIsomorphisms (fun i : I ↦ (p i).inverse)` on sheaves of SETS.
  Its stalk hypotheses use the same ordinary-module K-flat predicate at every i.
  Its conclusion is the source K-flatness predicate. There is no `Nonempty I`.
- There is no term-flatness condition and no upper or lower bound. Neither
  conjunct uses an arbitrary test functor as a substitute for a topos point.
  The assertion holds for EVERY normalized presentation, not just one selected
  family. The existence theorem on the new definition ensures that these
  presentation quantifiers do not introduce an unfulfilled extra hypothesis.

The module docstring and theorem docstring identify 0DEN and reproduce all six
DAG proof steps with their dependency IDs. The theorem proof is only `sorry`.
The new definition's only postponed proof is its separately named well-definedness
and existence theorem; its definition data is a structure with fully specified
fields and no `sorry`. No data definition selects an object from this theorem.

Recorded dependency declarations actually used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings` (00VH site convention).
- `Sheaf.CategoryTheory.Sites.GeometricMorphism`:
  `CategoryTheory.GeometricMorphism` (inverse, direct, adjunction, left exactness).
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, transparently Mathlib `SheafOfModules`.
- `Sheaf.Algebra.Homology.KFlat`:
  `CochainComplex.IsKFlatIndependentCoefficients`, exactly its recorded predicate.
- `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`:
  `CategoryTheory.MorphismProperty.kFlat`, as applied to ordinary module cochains.
  The public import of `WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat`
  supplies its cochain monoidal specialization (the source's
  `CochainComplex.kFlat_iff_preservesQuasiIso` is definitionally this predicate).

All already recorded proof-dependency modules are ordinary proof imports. The
four proof nodes without Lean records (restriction K-flatness, local stalk
realization, universal acyclic module test, and geometric inverse-image exactness)
are future proof infrastructure; their notions are not needed to type this
statement and no invented replacement is supplied.

Edge cases checked mathematically: the zero ring, zero complex, zero module,
empty underlying site and degenerate topos introduce no excluded case; in the
pointless case the forward universal quantifier is valid. An empty conservative
family forces every set-sheaf morphism to be invertible, so the degenerate
converse remains valid. An empty family on a nondegenerate topos fails the
explicit conservativity hypothesis. Arbitrarily unbounded complexes are tested
by direct-sum total tensor; no finite-product interchange or flatness of their
terms is asserted. The three site/coefficient universes and the family-index
universe are independent. There is no disputed statement or source correction.

Searches for the item: msearch LeanFinder query "A complex of sheaves of modules
on a ringed site is K flat if and only if its stalks at a conservative family of
points are K flat" returned ordinary flatness of scheme stalk maps and modules,
not K-flat complexes. Loogle `"KFlat"` returned only
`Lean.mkFlatCtorOfStructCtorName`. Mathlib grep `KFlat|kFlat|K.flat|stalk.*tensor`
in Algebra/Homology returned zero hits. Upstream rg for the item's blueprint ID
returned no declaration. Upstream and project rg for KFlat/kFlat found the
recorded predicates, term-flat pullback, and topological-space stalk criteria;
none states this result for arbitrary ringed sites and arbitrary geometric
morphism points. The upstream ordinary-module predicate's full signature and
both recorded sheaf predicates were read, rather than inferred from their names.

## New nodes

`def-sfb-ringed-site-point` defines normalized ring and module inverse images
at an arbitrary geometric-morphism point and states their existence. Its source
is 00YV for ring/group operations, 03D2 for variable-ring scalar action, and the
point specialization of 0DEN. All dependencies are existing recorded definitions.
The Lean structure and existence theorem match its clauses: `ring`,
`ringUnderlying`, `modules`, `moduleUnderlying`, the ring and module graph
conditions, and `modules_additive`. `RingedSitePoint.nonempty` is the separately
named proof that these exact finite-product transport data exist; its docstring
supplies the construction and axiom verification step by step.

This is not another general sheaf-to-sheaf `AlgebraicInverseImage` definition:
that interface requires a target site, a target ring SHEAF, and a functor into
module SHEAVES. It cannot take the node's arbitrary given `p.inverse` with target
`Type w` or produce ordinary `ModuleCat R_p` objects without an additional
site presentation and equivalence. The new interface expresses precisely this
missing point specialization, keeping the given point unchanged. The existing
`ConstantLeftModuleInverseImage`/`sitePointModuleEvaluation` interfaces fix a
constant coefficient ring and do not handle the variable ring sheaf R. The
existing topological module stalk functor assumes a ringed topological space.
None is copied or replaced in its original scope.

DAG rg and `blueprint_refs.py search 'point stalk ring modules inverse image'`
found no node with this definition (the blueprint query returned zero). The
candidate `lem-trf-site-point-fibre` was opened: its conclusion is for constant
coefficients and a finite-limit site. The algebraic inverse-image node and
source were opened as well and have the target-site requirement just described.
The new node records the actual three search outputs verbatim. They are:

```text
[leansearch] OK 8 hit(s)
  {"name": "CategoryTheory.GrothendieckTopology.Point.sheafFiber", "module": "Mathlib.CategoryTheory.Sites.Point.Basic", "type": ": Sheaf J A ⥤ A", "doc": "The functor from sheaves on a category $\\mathcal{C}$ with values in $\\mathcal{A}$ to $\\mathcal{A}$, obtained by composing the inclusion of sheaves into presheaves with the presheaf fiber functor at a "}
  {"name": "SheafOfModules.instIsLeftAdjointPullback", "module": "Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous", "type": ": (pullback.{v} φ).IsLeftAdjoint", "doc": "Given categories $\\mathcal{C}$ and $\\mathcal{D}$ with Grothendieck topologies $J$ and $K$, a continuous functor $F : \\mathcal{C} \\to \\mathcal{D}$, and a natural transformation $\\phi : S \\to F_*R$ betw"}
  {"name": "SheafOfModules.pullback", "module": "Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous", "type": ": SheafOfModules.{v} S ⥤ SheafOfModules.{v} R", "doc": "Given categories $\\mathcal{C}$ and $\\mathcal{D}$ with Grothendieck topologies $J$ and $K$, a continuous functor $F : \\mathcal{C} \\to \\mathcal{D}$, and a natural transformation $\\phi : S \\to F_*R$ betw"}
  {"name": "PresheafOfModules.hasFiniteLimits", "module": "Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits", "type": ": HasFiniteLimits (PresheafOfModules.{v} R)", "doc": "For any presheaf of rings $ R $ on a category $ \\mathcal{C} $, the category of presheaves of modules over $ R $ has all finite limits. This means the category admits constructions such as products, eq"}
  {"name": "PresheafOfModules.pushforward₀", "module": "Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward", "type": "(R : Dᵒᵖ ⥤ RingCat.{u}) : PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} (F.op ⋙ R)", "doc": "Given a functor $ F : \\mathcal{C} \\to \\mathcal{D} $ and a presheaf of rings $ R : \\mathcal{D}^{\\text{op}} \\to \\mathbf{Ring} $, this defines the pushforward functor $ F_* $ that maps presheaves of modu"}
  {"name": "AlgebraicGeometry.StructureSheaf.comap_id'", "module": "Mathlib.AlgebraicGeometry.StructureSheaf", "type": "(U : Opens (PrimeSpectrum.Top R)) :\n  (comap (RingHom.id R) U U fun p hpU => by rwa [PrimeSpectrum.comap_id]) = RingHom.id _", "doc": "For any commutative ring $ R $ and open set $ U $ in the prime spectrum $ \\operatorname{Spec}(R) $, the inverse image sheaf of the identity ring homomorphism $ \\operatorname{id}_R : R \\to R $ on $ U $"}
  {"name": "AlgebraicGeometry.LocallyRingedSpace.isLocalHomStalkMap'", "module": "Mathlib.Geometry.RingedSpace.LocallyRingedSpace", "type": "{X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X) : IsLocalHom (f.toHom.stalkMap x).hom", "doc": "For any morphism $f : X \\to Y$ between two locally ringed spaces, and for any point $x \\in X$, the ring homomorphism $\\mathcal{O}_{Y, f(x)} \\to \\mathcal{O}_{X, x}$ induced by $f$ at $x$ is a local rin"}
  {"name": "AlgebraicGeometry.Spec.preimage", "module": "Mathlib.AlgebraicGeometry.GammaSpecAdjunction", "type": ": R ⟶ S", "doc": "The function constructs the preimage of a morphism from a scheme $X$ to $\\operatorname{Spec}(S)$ under the contravariant Spec functor, corresponding to a ring homomorphism $S \\to \\Gamma(X, \\mathcal{O}"}
```

```text
[leanfinder] OK 8 hit(s)
  {"name": "AlgebraicGeometry.StructureSheaf.to_global_factors_apply", "module": "Mathlib/AlgebraicGeometry/StructureSheaf", "type": "∀ (R : Type u) [inst : CommRing R] (x : CategoryTheory.ToType { carrier := R, commRing := inst }),\n  (CategoryTheory.ConcreteCategory.hom (AlgebraicGeometry.StructureSheaf.toOpen R ⊤)) x =\n    (CategoryTheory.ConcreteCategory.hom ((AlgebraicGeometry.Spec.structureSheaf R).val.map (CategoryTheory.eqT", "doc": "For any commutative ring $ R $, the canonical ring homomorphism from $ R $ to the global sections of the structure sheaf $ \\mathcal{O}_{\\operatorname{Spec}(R)} $ over the entire prime spectrum $ \\oper"}
  {"name": "AlgebraicGeometry.StructureSheaf.toOpen_comp_comap_apply", "module": "Mathlib/AlgebraicGeometry/StructureSheaf", "type": "∀ {R : Type u} [inst : CommRing R] {S : Type u} [inst_1 : CommRing S] (f : R →+* S)\n  (U : TopologicalSpace.Opens ↑(AlgebraicGeometry.PrimeSpectrum.Top R))\n  (x : CategoryTheory.ToType { carrier := R, commRing := inst }),\n  (AlgebraicGeometry.StructureSheaf.comap f U\n        ((TopologicalSpace.Opens", "doc": "For a commutative ring $ R $ and an open subset $ U $ of its prime spectrum $ \\operatorname{Spec}(R) $, there exists a canonical ring homomorphism from $ R $ to the ring of sections $ \\mathcal{O}(U) $"}
  {"name": "AlgebraicGeometry.ΓSpec.toOpen_comp_locallyRingedSpaceAdjunction_homEquiv_app", "module": "Mathlib/AlgebraicGeometry/GammaSpecAdjunction", "type": "∀ {X : AlgebraicGeometry.LocallyRingedSpace} {R : Type u} [inst : CommRing R]\n  (f : AlgebraicGeometry.LocallyRingedSpace.Γ.rightOp.obj X ⟶ Opposite.op { carrier := R, commRing := inst })\n  (U :\n    (TopologicalSpace.Opens\n        ↑↑(AlgebraicGeometry.Spec.toLocallyRingedSpace.obj\n                (O", "doc": "For a locally ringed space $X$ and commutative ring $R$, the composition of the structure sheaf morphism $\\mathcal{O}_{\\operatorname{Spec}(R)}(U) \\to R$ with the component of the Γ-Spec adjunction hom"}
  {"name": "AlgebraicGeometry.LocallyRingedSpace.toToΓSpecMapBasicOpen", "module": "Mathlib/AlgebraicGeometry/GammaSpecAdjunction", "type": "(X : AlgebraicGeometry.LocallyRingedSpace) →\n  (r : ↑(AlgebraicGeometry.LocallyRingedSpace.Γ.obj (Opposite.op X))) →\n    X.presheaf.obj (Opposite.op ⊤) ⟶ X.presheaf.obj (Opposite.op (X.toΓSpecMapBasicOpen r))", "doc": "The morphism from the global sections of the structure sheaf of a locally ringed space $X$ to the sections over the basic open set $X_{D(r)}$ (preimage of $D(r)$ under the Γ-Spec map), induced by the "}
  {"name": "AlgebraicGeometry.Scheme.ΓSpecIso_inv", "module": "Mathlib/AlgebraicGeometry/Scheme", "type": "∀ (R : CommRingCat), (AlgebraicGeometry.Scheme.ΓSpecIso R).inv = AlgebraicGeometry.StructureSheaf.toOpen ↑R ⊤", "doc": "The global sections of the structure sheaf on the affine scheme $\\operatorname{Spec}(R)$ over its entire space are naturally isomorphic to the commutative ring $R$."}
  {"name": "AlgebraicGeometry.LocallyRingedSpace.toΓSpecSheafedSpace_hom_c_app", "module": "Mathlib/AlgebraicGeometry/GammaSpecAdjunction", "type": "∀ (X : AlgebraicGeometry.LocallyRingedSpace)\n  (X_1 :\n    (TopologicalSpace.Opens\n        ↑(AlgebraicGeometry.PrimeSpectrum.Top ↑(AlgebraicGeometry.LocallyRingedSpace.Γ.obj (Opposite.op X))))ᵒᵖ),\n  X.toΓSpecSheafedSpace.hom.c.app X_1 =\n    CategoryTheory.yoneda.preimage ((CategoryTheory.Functor.IsCo", "doc": "For any locally ringed space $X$ and any open subset $X_1$ of $\\operatorname{Spec}(\\Gamma(X))$, the component of the natural transformation $c$ at $X_1$ equals the preimage under the Yoneda embedding "}
  {"name": "AlgebraicGeometry.LocallyRingedSpace.toΓSpecSheafedSpace_app_eq", "module": "Mathlib/AlgebraicGeometry/GammaSpecAdjunction", "type": "∀ (X : AlgebraicGeometry.LocallyRingedSpace) (r : ↑(AlgebraicGeometry.LocallyRingedSpace.Γ.obj (Opposite.op X))),\n  X.toΓSpecSheafedSpace.hom.c.app (Opposite.op (PrimeSpectrum.basicOpen r)) = X.toΓSpecCApp r", "doc": "For a locally ringed space $X$ and element $r$ in its global sections $\\Gamma(X)$, the component of the natural transformation $\\Gamma$-Spec at the basic open set $D(r)$ coincides with the canonical l"}
  {"name": "AlgebraicGeometry.ΓSpec.toSpecΓ_unop", "module": "Mathlib/AlgebraicGeometry/GammaSpecAdjunction", "type": "∀ (R : CommRingCatᵒᵖ),\n  AlgebraicGeometry.toSpecΓ (Opposite.unop R) = AlgebraicGeometry.StructureSheaf.toOpen ↑(Opposite.unop R) ⊤", "doc": "For any commutative ring $ R $, the canonical ring homomorphism from $ R $ to the global sections $ \\mathcal{O}_{\\operatorname{Spec}(R)}(\\operatorname{Spec}(R)) $ of its prime spectrum coincides with "}
```

```text
[grep] OK 3 hit(s)
  {"file": "Mathlib/CategoryTheory/Preadditive/Yoneda/Basic.lean", "line": "17", "text": "object `X` to the group of morphisms `X ⟶ Y`. At each point, we get an additional `End Y`-module"}
  {"file": "Mathlib/CategoryTheory/Preadditive/Yoneda/Basic.lean", "line": "55", "text": "object `X` to the group of morphisms `X ⟶ Y`. At each point, we get an additional `End Y`-module"}
  {"file": "Mathlib/CategoryTheory/Preadditive/Yoneda/Basic.lean", "line": "81", "text": "object `Y` to the group of morphisms `X ⟶ Y`. At each point, we get an additional `End X`-module"}
```

Direct rg in upstream WeilConjectures/CategoryTheory and
WeilConjectures/Algebra/Category/ModuleCat found no variable-ring algebraic point
inverse-image construction. Project rg found only the sheaf-target interface,
constant-coefficient point lifts and topological/scheme-specific stalks described
above. The names `CategoryTheory.RingedSitePoint` and
`CochainComplex.ringedSite_kFlat_stalk_criterion` did not occur in either library
before this delivery.

## Validation

The prescribed scompile.py wrapper is used for each delivered file separately,
in dependency order. Initial compilation of the helper succeeded with two style
warnings; both overlong lines were shortened before the final compile. The paired
compile completed successfully for both files with no errors or warnings. The
final packet also imports the site-definition dependency explicitly; the delivery
dry run recompiles that final content before preflight.

## Second reading by N8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
