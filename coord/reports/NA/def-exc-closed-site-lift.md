## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtale.ClosedSiteLift` defines both functors of
blueprint definition 1843 without changing the node statement or its dependencies.
Its main declaration is `AlgebraicGeometry.Scheme.AffineProEt.closedSiteLift`.
All definitions contain actual constructions; no theorem is proved.

Hypothesis and clause correspondence:

- A commutative ring A is `(A : Type u) [CommRing A]`; its ideal is `(I : Ideal A)`.
  The two bases are exactly the recorded `(Spec (.of A)).AffineProEt` and
  `(Spec (.of (A ⧸ I))).AffineProEt`. There is no finiteness, nonzero-ring,
  proper-ideal, or extra affine-presentation hypothesis.
- `u` is `closedSiteBaseChange A I`: the existing
  `CategoryTheory.MorphismProperty.Over.pullback`, applied to
  `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))`. Its objects are fibre products
  and its maps the induced pullback maps, in the recorded full basis categories.
- For an object V, its coordinate algebra is Γ(V.left, ⊤), with A-algebra map
  `(Scheme.ΓSpecIso (.of A)).inv ≫
  (V.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop`.
  `closedSiteCoordinates` bundles this in `CommAlgCat A`. For V = Spec C this is
  canonically C with the specified A-algebra structure, by ΓSpecIso; general affine
  V is identified with its spectrum by isoSpec. This uses the actual affine
  schemes of the recorded basis, rather than replacing them by a new category.
- `v(V) = Spec H_A(C)` is `closedSiteLiftObj`: its structure map is the spectrum
  of `algebraMap A (Algebra.ClosedLift A (closedSiteCoordinates A I V))`.
  The named proposition `closedSiteLift_mem` supplies membership in the indicated
  basis. Its docstring explains filteredness, filtered-colimit stability, and the
  affine spectrum characterization; its proof is postponed, not its data.
- The map clause is `closedSiteLiftMap`: it applies `Spec.map` to the ring map
  underlying the recorded `Algebra.ClosedLift.map`, applied to the pullback of
  functions `f.left.appTop`. Thus both contravariances have the required direction.
  `closedSiteCoordinates_commutes` and `closedSiteLiftMap_over` state the necessary
  algebra and over-category compatibility. `closedSiteLiftMap_id` and
  `closedSiteLiftMap_comp` supply the functor laws. Each has a natural-language
  proof in its docstring and `sorry` as its entire proof.
- `closedSiteLift` bundles exactly these object and map constructions. The
  underlying basis categories and their topologies are reused unchanged: this
  node defines functors on those categories, not a continuity assertion.

Dependency declarations inspected and reused:

- `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`:
  `AlgebraicGeometry.Scheme.AffineProEt`, its category structure, `AffineProEt.mk`,
  `AffineProEt.toProEt`, `AffineProEt.precoverage`, and `AffineProEt.topology`.
  Read the exact group-clone source and `coord/pefw-upstream-framework.md`.
- `Sheaf.RingTheory.ProEtale.ClosedLiftMap`: `Algebra.ClosedLift.map`, with
  `postcomp`, `ι_map`, and the underlying upstream `Algebra.ClosedLift`, `Index`,
  `diagram`, `toAlgHom`. No second algebra-lift construction is introduced.
- `WeilConjectures.RingTheory.ProEtale.ClosedLift`:
  `Algebra.ClosedLift.isFiltered_index` and its filtered colimit presentation.
  Its module is already publicly imported by `ClosedLiftMap`.
- `Sheaf.RingTheory.IndEtaleStability`:
  `RingHom.indEtale_principalZariski_stability`, especially its filtered-colimit
  and base-change clauses, is imported for the membership justification.
- Existing Mathlib `MorphismProperty.Over.pullback`, `CommAlgCat.of`, global
  sections, `ΓSpecIso`, and `Spec.map` are used directly.

Edge cases checked: A may be the zero ring; I may be bottom or top; V may be the
empty affine scheme (zero coordinate ring). Quotients, global sections, the
closed-lift colimit, and pullbacks all remain defined. In particular no assumption
that I is proper or that V is inhabited was added. All objects and rings are in a
single explicit universe u, matching the existing site encoding; no independent
smaller universe excludes large rings. All variables and universes are bound.

Searches made with `msearch.py NA def-exc-closed-site-lift` (logged in the sandbox):

- LeanFinder: `Functor lifting affine ind etale schemes over A/I to Spec of closed
  lift colimit over A`. Eight hits concern affine transition limits, quotient
  lifts, ideal subschemes, and the etale forgetful functor; none is this functor.
- Loogle: `"Etale", "Functor"`. Two hits, the cofiltered geometric-point indexing
  category and the finite-etale equivalence over a separably closed field;
  neither constructs this closed-site lift.
- Mathlib grep: `ClosedLift|closedSiteLift|closed.*lift`, in AlgebraicGeometry.
  Fourteen hits on closed immersions, transition limits, and ideal subschemes;
  none gives the closed-lift algebra/site functor.
- LeanSearch: `Functor lifting affine ind etale schemes over a quotient ring
  using etale neighborhood colimits`. Service unavailable (Internal Server Error).
- Source `rg`: `ClosedLift|closedLift`, and
  `AffineProEt.*(pullback|baseChange)|def.*closed.*[Ll]ift`; source id grep
  `def-exc-closed-site-lift`. Found the existing algebra lift and the object/map
  family for closed-cover extension, not a functor on the affine basis. The
  latter family has extra open-cover summands and is not this node's definition.
- Project `rg`: `closedSite|ClosedSite|ClosedLift|closedLift` in `lean/Sheaf`.
  Found only the algebra-map and units modules, not this site construction.
  The proposed declaration names have no existing match.

No node faults, statement disputes, new nodes, or dependency replacement modules.
Validation uses only `scompile.py` on the server, with nice 19, two threads and
60 seconds per file. No local Lean compiler or library build was run.


## Second reading by NA

I independently read the item JSON and its blueprint source (definition 1843),
Stacks `proetale.tex`, Tags 097P (`lemma-lift-ind-etale`) and 09BK
(`lemma-closed-immersion-affines`), and the delivered Lean module. The source
assumes only a commutative ring A and an arbitrary ideal I. The statements about
adjoints, reductions, specialization and coverings in 09BK belong to subsequent
nodes; this definition asks for the two functors and their actual constructions.
The item has no statement correction and no new nodes or dependency modules.

Object, hypothesis and conclusion checklist (all verdicts PASS):

1. A commutative ring A, an ideal I, X = Spec A and Z = Spec(A/I):
   `variable (A : Type u) [CommRing A] (I : Ideal A)` and the two displayed
   `Spec (.of ...)` bases give exactly these data. No Noetherian, nontriviality,
   nilpotence, finite-presentation-of-I or proper-ideal hypothesis is added.
2. The indicated full affine ind-etale bases: the domains and codomains use the
   dependency's exact `Scheme.AffineProEt`. I opened the group-clone
   `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`: this is
   `proAffineEtale.Over ⊤ S`, with all over-morphisms allowed. Its `mk`, `toProEt`,
   induced precoverage and topology are the dependency's declarations. I also
   read `proAffineEtale_Spec_iff` and `proAffineEtale_iff_appTop`; for affine bases
   these identify the objects with precisely affine ind-etale schemes. No new
   site or topology is defined here. I read `coord/pefw-upstream-framework.md`.
3. Base change u from the X basis to the Z basis: `closedSiteBaseChange A I`
   applies `MorphismProperty.Over.pullback` to the spectrum of
   `Ideal.Quotient.mk I`. I opened `OverAdjunction.lean`: its objects are the
   fibre products with structure morphism `pullback.snd`, and maps are the
   induced pullback maps. Its required pullback and stability instances are
   available for this morphism; they are not extra hypotheses on A or I.
4. V = Spec Cbar over Z, with Cbar an ind-etale A/I-algebra regarded over A:
   `closedSiteCoordinates A I V` is the actual global-section ring of V. Its
   A-action is the map induced by the composite V -> Spec(A/I) -> Spec A,
   precomposed with `(Scheme.ΓSpecIso (.of A)).inv`. On V = Spec Cbar, ΓSpecIso
   identifies it with Cbar with the required A-action. Affineness is supplied
   by V's membership in the recorded basis, not a new assumption.
5. v(V) = Spec H_A(Cbar): `closedSiteLiftObj` uses `AffineProEt.mk` on precisely
   the spectrum of `algebraMap A (Algebra.ClosedLift A
   (closedSiteCoordinates A I V))`. This is the dependency's colimit algebra,
   not a chosen arbitrary lift. `closedSiteLift_mem` asserts membership in the
   indicated basis. Its proof plan uses filteredness and ind-etale stability,
   as the node specifies, followed by `proAffineEtale_Spec_iff`.
6. Maps are opposite to the algebra construction's maps:
   `closedSiteCoordinatesMap A I f` has direction coordinates(W) -> coordinates(V)
   for f : V -> W. Its underlying map is exactly `f.left.appTop.hom`.
   `closedSiteCoordinates_commutes` supplies only the required compatibility
   with A. `closedSiteLiftMap` applies `Spec.map` to the dependency's
   `Algebra.ClosedLift.map` of that map; this second reversal gives v(V) -> v(W).
   `closedSiteLiftMap_over` is exactly its structural triangle over Spec A.
7. These constructions are functors: `closedSiteLift` bundles the preceding
   object and map formulas, with `closedSiteLiftMap_id` and
   `closedSiteLiftMap_comp` stating the identity and composition laws. All
   quantifiers in these statements are over arbitrary objects and morphisms of
   the required basis. The conclusions assert no additional geometric property.

I opened every dependency record and the exact declarations it names:
`Algebra.ClosedLift.Index`, its compatible-map category, `diagram`, the concrete
colimit `Algebra.ClosedLift`, `toAlgHom`, `isFiltered_index` and its ind-etale
presentation; `Sheaf.RingTheory.ProEtale.ClosedLiftMap`'s `postcomp`, `map` and
`ι_map`; and `RingHom.indEtale_principalZariski_stability`, in particular base
change and filtered colimits. The small closed-lift model uses finite-variable
polynomial quotients and all compatible algebra maps, as the dependency record
explains. No dependency signature is replaced by a similarly named notion.

Edge cases: the zero ring A, I = bottom, I = top, and empty affine V are all
allowed. Global sections of empty V are the zero ring; no nonzero-coordinate or
inhabited-scheme condition occurs. For the closed-lift indexing category the
factorization through A (zero variables and zero relation ideal) supplies an
object even for zero input, so no empty-index assumption is hidden. There is no
external index set, degree n or characteristic restriction. The arbitrary
universe u consistently covers the rings and schemes of the recorded sites;
the basis lives in Type (u+1), with morphisms in the existing category. Every
variable and universe is bound.

Independent H4 searches, recorded by `msearch.py` in `searches.jsonl`:

- LeanFinder: `Functor sending affine schemes over a quotient to spectra of
  colimits of etale algebra factorizations`. Eight results: affine transition
  limits, affine-scheme colimits/inclusion/Spec, liftQuotient, ideal subschemes,
  affine space and affine covers. None defines this closed-site functor.
- Loogle: `"Spec", "lift"`. Twelve results, all Std.Do specification/monad-lift
  lemmas; no matching algebraic-geometric declaration.
- LeanSearch: `Affine ind etale site functor lifting schemes along a closed
  immersion using a filtered colimit`. Service unavailable (Internal Server
  Error), recorded without treating that failure as a no-match result.
- Independent rg searches in Mathlib's algebraic-geometric sites and ideal-sheaf
  modules, upstream WeilConjectures and project lean/Sheaf used `closedSite`,
  `ClosedSite`, `closed_site`, `ClosedLift.map`, `lift.*[Ss]ite`,
  `[Ss]ite.*lift` and base-change names. I opened the closest upstream candidate,
  `AlgebraicGeometry.ProEtale.ClosedCoverExtension`: `closedLiftCoverObj` and
  `closedLiftCoverHom` form a family with additional basic-open summands and
  have no action on arbitrary basis morphisms. They are not this functor.
  The existing Over.pullback and ClosedLift algebra/map are reused here.

No H3, H4 or H5 mismatch was found. Every definition supplies actual data; all
five theorem proofs remain whole named `sorry` proofs, with source, blueprint id
and a complete proof plan in their docstrings. The node has no proof steps to
omit. The module and every declaration have the required source docstrings.
The recorded `lean.statement` is verbatim the main signature through its return
type. No local notation, local instance, private copy or unbound binder occurs.

Repair: changed `public import Sheaf.RingTheory.IndEtaleStability` to plain
`import`, because this theorem is needed only for the postponed membership
proof, following the stage-2 import convention. No definition, theorem signature,
node statement or dependency record needed alteration. The original file passed
scompile.py; the final file is recompiled by the required delivery dry run and
actual delivery, using the server-only nice-19/two-thread/60-second-per-file gate.
