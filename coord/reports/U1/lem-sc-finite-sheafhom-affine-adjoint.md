## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteSheafHomAffineAdjoint` states
`AlgebraicGeometry.exists_affine_derivedSheafHom_adjunction`, with proof `sorry`.
It changes only the item's `lean` record; no new definitions or dependency modules
are needed. All existential functors and isomorphisms are witnesses in the theorem,
not replacement definitions of any existing notion.

Hypothesis and clause correspondence:

- Schemes and the affine morphism `f:Y→X`: `{X Y : Scheme.{u}} (f : Y ⟶ X)
  [IsAffineHom f]`. There is no finiteness, Noetherian, quasi-coherence or boundedness
  assumption.
- `A=f_*O_Y`: existential ring sheaf `A` is constrained to equal the continuous
  sheaf pushforward of `Y.ringCatSheaf` along `Opens.map f.base`.
  `HEq α f.toRingCatSheafHom` fixes the map `α:O_X→A` to the actual structure map;
  heterogeneous equality handles its dependent target. These witnesses simply name
  the specified objects, not arbitrary algebra sheaves or maps.
- The categories are the full unbounded derived categories of sheaves of modules:
  `DerivedCategory (SheafOfModules.{u} A)` and `schemeDerivedCategory X`.
  The shared `HasDerivedCategory.{w}` binder fixes the O_X localization. The
  corresponding localization for A-modules is existentially supplied in that same
  morphism universe, not assumed as an additional geometric hypothesis.
- Restriction of scalars is the existing `SheafOfModules.restrictScalars α`:
  `T` is constrained equal to it. Its derived functor `L` is identified by the
  natural isomorphism `t : Q ⋙ L ≅ T.mapHomologicalComplex (.up ℤ) ⋙ Q`.
  Thus it is restriction on complexes followed by localization, not an arbitrary
  left adjoint.
- `M` is the underlying O_X-module of A: `m : M ≅ (restrictScalars α).obj (unit A)`.
  `B` is the existing underived internal Hom functor from M, through
  `i : B ≅ (SheafOfModules.homFunctor X.sheaf).obj (op M)`.
  Additivity witnesses are existentially supplied to use Mathlib's termwise
  functor, not extra hypotheses on f.
- Right adjoint with its A-module values: `R : D(O_X) ⥤ D(A)` and `adj : L ⊣ R`.
  The natural isomorphism `d : R ⋙ L ≅ (Functor.curry.obj (derivedInternalHom ...)).obj
  (op ((DerivedCategory.singleFunctor _ 0).obj M))` identifies the underlying
  O_X-valued functor with the dependency's actual derived internal Hom from A.
  The A-module structure is the one characterized by this adjunction and its
  evaluation counit, rather than an unconstrained extra action assumption.
- Counit evaluation at the unit: the underived natural transformation
  `ε : B ⟶ 𝟭` is constrained at EVERY sheaf F and EVERY open U to send φ, transported
  by `i`, to its component on `Over.mk (𝟙 U)` applied to the section
  `(m.inv.val.app (op U)).hom 1`. This is evaluation at A's actual unit, transported
  to M; it is not an arbitrary global section.
- The derived counit clause is the final equality
  `adj.counit.app (Q.obj I) = (b I hI).hom ≫ Q.map ((NatTrans.mapHomologicalComplex
  ε (.up ℤ)).app I)`. Here `b` identifies the restricted right adjoint on each
  K-injective I with Q of its degreewise underived Hom. The preceding naturality
  equality requires this comparison to commute with EVERY chain map between
  K-injective complexes. Consequently the displayed counit is the induced
  evaluation morphism. Every derived object has a K-injective representative;
  adjunction naturality transports this equality to every K. Choosing such a
  representative is the calculation prescribed in the node's proof.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
  Read their full definitions: a locally ringed space with local affine charts,
  and a morphism of the underlying locally ringed spaces.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `AlgebraicGeometry.schemeDerivedCategory`.
  Read its full signature and docstring: the shared localization of
  `SheafOfModules.{u} (moduleRings X.toRingedSpace)`.
- `Sheaf.Algebra.Homology.DerivedInternalHom`: `CategoryTheory.derivedInternalHom`.
  Read its definition, full signature and comparison docstrings: the lift of the
  Hom complex with functorial K-injective replacement in the second variable.
- Existing sheaf-Hom API: `SheafOfModules.homFunctor`, `SheafOfModules.homObj`
  from `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`; existing
  restriction from `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`.
- Also read the proof dependency module `Sheaf.AlgebraicGeometry.FiniteSheafHomAffine`
  in full. Its theorem identifies the canonical A-action and evaluation counit.
  It is cited in the natural-language proof, not assumed in the signature.

Edge cases checked before writing: f can be the identity, in which case A=O_X
and the adjunction is the identity adjunction. Empty schemes and zero complexes
are included; evaluation at the unit of the zero ring is well typed. Arbitrary
unbounded K and arbitrary O_X-modules are included, with no finite generation,
flatness, coherence, field or characteristic restriction. No affine-open condition
is added to the counit formula: it holds on every open. Both geometric and derived
morphism universes are explicitly bound (`u w`), and auto-implicits are disabled
by the compiler command. No new data definition has a `sorry`.

Searches for an existing statement:

- `msearch.py leansearch`: “The restriction of scalars functor on derived categories
  of sheaves of modules has right adjoint derived internal Hom”. Service unavailable
  (Internal Server Error), recorded without a mathematical verdict.
- `msearch.py leanfinder`: “For an affine scheme morphism restriction of scalars on
  derived categories of sheaf modules is left adjoint to derived internal Hom, with
  counit evaluation at one”. Eight hits, including scheme pullback/pushforward and
  open-immersion restriction adjunctions; none is this statement.
- `msearch.py loogle`: `CategoryTheory.Adjunction, ModuleCat`. Twelve hits, including
  `ModuleCat.restrictCoextendScalarsAdj` for ordinary ring modules; not the derived
  sheaf adjunction.
- `msearch.py grep`: `restrictScalars|coextendScalars` in
  `Algebra/Category/ModuleCat/Sheaf`. Existing sheaf restriction and pushforward;
  no derived internal-Hom right-adjoint statement.
- `rg` in source `WeilConjectures` and project `lean/Sheaf` for the node id and
  `coextendScalars`: constant coefficient and étale scalar extension results only.
  Concept searches for sheaf Hom, restriction and derived Hom located the three
  dependency modules and the underived affine theorem above.
- `rg` for the proposed full declaration name in the upstream-name index,
  Mathlib, WeilConjectures and Sheaf: no existing declaration.

The local literature checkout has no `stacks-project/duality.tex`, so the stated
source was read on the official Stacks website: [0BV0](https://stacks.math.columbia.edu/tag/0BV0),
[0BUZ](https://stacks.math.columbia.edu/tag/0BUZ), and
[0AX3](https://stacks.math.columbia.edu/tag/0AX3). The first gives the derived
adjunction; the latter describes the map induced by O_X→A. The proof docstring
carries the node's three steps. No statement correction or dispute is needed.

Validation: `lcompile.py` compiled the final module cleanly (no errors or warnings).
The server compilation and delivery preflight are run by `deliver2.py --no-push`.
The independent second-reading section is intentionally left for the second reader.

## Second reading by U1

I read the node, its dependency records, the source tags, and the complete Lean
statement independently.  The correspondence is as follows.

- The node's objects `X`, `Y`, and `f : Y ⟶ X`, with `f` affine, render as
  `{X Y : Scheme.{u}}`, `(f : Y ⟶ X)`, and `[IsAffineHom f]`.
- `A = f_* O_Y` and the structure map `O_X ⟶ A` render as the existential
  `A : Sheaf (Opens.grothendieckTopology X) RingCat` and `α`, followed by the
  equality to `sheafPushforwardContinuous ... Y.ringCatSheaf` and
  `HEq α f.toRingCatSheafHom`.  This fixes the witnesses to the node's objects.
- The two derived categories render as `DerivedCategory (SheafOfModules A)` and
  `schemeDerivedCategory X`; the only external hypothesis is the shared
  `[HasDerivedCategory ... (moduleRings X.toRingedSpace)]`.  The A-side
  localization is an existential witness, not an added geometric hypothesis.
- Restriction of scalars renders as `T` with `T = SheafOfModules.restrictScalars α`;
  its derived functor is `L`, with comparison `t` to the localized termwise
  functor.  Thus the left adjoint is the specified restriction functor.
- The right adjoint renders as `R` and `adj : L ⊣ R`.  The comparison `d` identifies
  its underlying O_X-valued composite `R ⋙ L` with the fixed
  `derivedInternalHom` functor from the module `M` identified with A by `m`.
- The counit clause renders evaluation at the unit: `ε` is constrained at every
  sheaf and open, and the displayed equality evaluates the transported morphism
  on `(m.inv ...).hom 1`.  The final two clauses identify the derived counit with
  the localized degreewise counit on every K-injective representative and impose
  its naturality for every chain map.

The quantifier order and all conjunctions in the Lean signature agree with these
objects and clauses.  No finiteness, Noetherian, quasi-coherence, boundedness,
flatness, characteristic, field, or nonemptiness hypothesis is added.  The empty
scheme, identity affine map, zero sheaf/complex, and arbitrary unbounded complexes
remain covered; universes `u` and `w` are explicit.  The source section is headed
“Right adjoint of pushforward for finite morphisms”, but Tag 0BV0 itself says
“with notation as above” and the DAG node deliberately states the affine
generalization; I found no Lean mismatch with the node and therefore made no
statement correction.

I repeated the existing-definition searches with `msearch.py` (LeanSearch,
LeanFinder, and Loogle), `rg` over Mathlib, `WeilConjectures`, and `lean/Sheaf`,
and the upstream-name index.  They found only generic module restriction and
sheaf pushforward adjunctions, not this derived sheaf-Hom statement.  The module
uses the recorded declarations `schemeDerivedCategory`, `derivedInternalHom`,
`SheafOfModules.homFunctor`, `SheafOfModules.restrictScalars`, and the Mathlib
affine morphism class; no new notion or dependency module is required.

No mismatch was found.  The only change in this second reading is this report;
the Lean module and node statement are unchanged.  `lcompile.py` compiles the
module with no errors or warnings.

## Reviewer fix (R-fsa, stage 2)

The statement was restated by the reviewer; the correspondence above describes the delivered
form, not the landed one.

- A = f_*O_Y is now the landed `moduleRings (directImageAlgebraSpace f)` (def-sc-direct-image-algebra-derived-category, 256cc9ade) with the landed structure map `⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩` and a `[HasDerivedCategory.{wA} …]` binder, as in lem-sc-finite-affine-derived-equivalence; the existential ring sheaf `A` tied by `=`/`HEq` to a second spelling of the pushforward and the existential `HasDerivedCategory` instance are gone.
- The untied existentials are gone: the delivered counit clause went through a free natural iso `b` on K-injectives that was not tied to `d`, so it could not tell evaluation at 1 from its negative. Now the underived A-valued right adjoint `H` (with `iH : H ⋙ restrict ≅ homObj A (-)` and `adj₀`, counit = evaluation at 1) is given, `R` is a right derived functor of `H` with comparison `β` (`IsRightDerivedFunctor`), `L` is tied to restriction by `t`, `R ⋙ L` is absolute (`IsRightDerivedFunctor` of the whiskered `β`), `R ⋙ L ≅ RHom_{O_X}(A, -)`, and the derived counit is the morphism induced by the underived counit in the form of Mathlib `Adjunction.derivedε_fac_app`: `L.map (β.app K) ≫ adj.counit.app (Q K) = t.hom.app (H K) ≫ Q.map (adj₀.counit K)` for every complex K. The redundant `T`, `M`, `B`, `ε`, `b` binders were removed.
