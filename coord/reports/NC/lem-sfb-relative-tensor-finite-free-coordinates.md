## Worker report

The module `Sheaf.CategoryTheory.RelativeTensorFiniteFreeCoordinates` states
`CategoryTheory.sfb_relative_tensor_finite_free_coordinates` with `sorry` as its entire
proof. It records all the node's assertions together. No statement correction, new node,
or dependency-module repair is needed. The source read was the current blueprint at
`literature/blueprint/latest/blueprint/sec-proetale-coefficients/`
`sk-prop-sfb-cartesian-coefficients/lem-sfb-subfield-flat.proof.md`, last sentence:
finite freeness gives the relative tensor identification naturally in M. The full
seven-step expanded proof from this DAG node is in the theorem's docstring.

Hypothesis and clause correspondence (Lean composition `a ≫ b` means first a, then b):

- The essentially small site is `{C : Type uC} [Category.{vC} C]
  [EssentiallySmall.{w} C] (J : GrothendieckTopology C)`. The three universes are
  independently declared, and `set_option autoImplicit false` checks all binders.
  The coefficient category is `AddCommGrpCat.{w}` with its upstream integer tensor,
  imported from `WeilConjectures.CategoryTheory.RingObjects.Ab`; this is not the
  cartesian tensor. H is `Sheaf J AddCommGrpCat.{w}`.
- The ambient monoidal and symmetric structures are the fields of the recorded
  `sfbSheafTensorStructure J`. The auxiliary instance declarations only select these
  fields and existing API consequences. `sfbCoordinateSheafify` transports existing
  left exact sheafification from the small model, so no sheafification hypothesis is
  added. `sfbCoordinateSheafClosed` selects the right-adjoint structure certified by
  `sfbSheafTensor_properties`, which is unique up to natural isomorphism; it does not
  choose any undetermined object or tensor. Its purpose is to apply the existing
  `sfbSheafTensor_monoidalPreadditive` theorem. Both colimit preservation instances
  are projections of the existing properties theorem at diagram size zero.
- R is `(R : Sheaf J AddCommGrpCat.{w}) [MonObj R] [IsCommMonObj R]`.
  N is `Mod (Sheaf J AddCommGrpCat.{w}) R`, the recorded internal module category.
  The relative tensor and its unitors are the existing `Mod.monoidalCategory`.
  `Mod.tensorObjπ P M` is precisely the canonical coequalizer projection t.
  Forgetful objects and maps are rendered by `.X` and `.hom`, definitionally the
  object/map operations of `Mod.forget R`.
- The nonnegative integer n is `(n : ℕ)`, with no positivity hypothesis.
  The chosen basis is `θ : (⨁ fun _ : Fin n ↦ Mod.regular R) ≅ N`.
  The regular-module biproduct uses the existing
  `HasFiniteBiproducts.of_hasFiniteProducts` interface, selected by the auxiliary
  `sfbCoordinateModuleBiproducts` instance. Its finite products already exist by the
  upstream module-limits API. No alternate product or finite-free module is defined.
- The node's e_i is `biproduct.ι (fun _ : Fin n ↦ Mod.regular R) i ≫ θ.hom`.
  Its q_i is `θ.inv ≫ biproduct.π (fun _ : Fin n ↦ Mod.regular R) i`.
  The product projections rho_i are `Pi.π (fun _ : Fin n ↦ M) i`.
- L_M is `(λ_ M)` in the internal module category; the ambient unitor is `(λ_ M.X)`.
  The ring unit is `η[R]`, and its action is `γ[R,M.X]`.
- The initial universally quantified conjunction states both unitor normalizations:
  `Mod.tensorObjπ (Mod.regular R) M ≫ (λ_ M).hom.hom = γ[R,M.X]`, and
  `(λ_ M).inv.hom = (λ_ M.X).inv ≫ η[R] ▷ M.X ≫ Mod.tensorObjπ (Mod.regular R) M`.
  Here whiskering `a ▷ M.X` is the ambient tensor of a with the identity.
- `∃ D : tensorLeft N ≅ Functor.pi' (fun _ : Fin n ↦ 𝟭 ...) ⋙
  Limits.Pi.functor (Fin n), ...` is the natural isomorphism of module-valued
  functors. `tensorLeft` is the monoidal-category functor for the recorded relative
  tensor (not the alternate upstream explicit tensorLeft API). The target functor
  repeats each module n times and takes its categorical product; its map is f^n.
- The first conjunct under D is its projection formula, with `q_i ▷ M` followed by
  the relative left unitor. The second conjunct is the inverse formula, the sum
  over `Fin n` of rho_i followed by the inverse relative unitor and `e_i ▷ M`.
- The third conjunct under D states the underlying forward formula after composing
  with `Mod.tensorObjπ N M`, using the underlying q_i tensored with the identity and
  the action. The fourth conjunct is the underlying inverse sum: rho_i, inverse
  ambient unitor, `(η[R] ≫ e_i.hom) ▷ M.X`, then `Mod.tensorObjπ N M`.
  These are the exact arrows in the node, not replacements with sectionwise tensors.
- The last conjunct explicitly states naturality for every `(f : M ⟶ M')`:
  `(N ◁ f) ≫ (D.app M').hom = (D.app M).hom ≫ Limits.Pi.map (fun _ : Fin n ↦ f)`.
  This also follows from the natural-isomorphism type, but it is explicitly present
  to match the node's displayed equation.

Dependency declarations inspected and used:

- `sk-def-sfb-sheaf-tensor`: `Sheaf.CategoryTheory.SheafTensor`,
  `CategoryTheory.sfbSheafTensor_properties` and
  `CategoryTheory.sfbSheafTensor_monoidalPreadditive`; the canonical
  `CategoryTheory.sfbSheafTensorStructure` is from its public structure dependency.
- `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod`,
  `CategoryTheory.Mod`, `ModObj`, `Mod.Hom`, `Mod.regular`, and `Mod.forget`.
- `def-sfb-modobj-relative-tensor`:
  `WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`,
  `CategoryTheory.Mod.monoidalCategory`, `Mod.tensorObj_X`, `Mod.tensorObjπ`, and
  `Mod.isColimitTensorπ`. Its public preadditive dependency provides module sums.
- Proof-only dependencies have imports as required: `Mathlib.CategoryTheory.Sites.Sheafification`
  for `def-weil-pbc-sheafification` (`presheafToSheaf`, `toSheafify`,
  `sheafificationAdjunction`), and `Mathlib.CategoryTheory.Monoidal.Bimod` for
  `lem-sfb-bimod-monoidal` (`Bimod.monBicategory`, induced endomorphism monoidal
  category, and the action-induced `leftUnitorBimod`). The existing
  `GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian` and
  `hasSheafifyEssentiallySmallSite` supply left exact sheafification in the helper.

Edge cases checked mathematically before drafting: n=0 gives a zero regular-module
biproduct, N is zero via θ, the target product is terminal/zero, projection clauses
are vacuous, and inverse sums are empty zero maps. No binder excludes this case.
For n=1 the isomorphism reduces to the chosen basis and the relative unitor. For
M=0 all formulas are equations between zero arrows. For the zero ring object every
module is zero by unitality, consistent with both normalizations. The empty site or
degenerate sheaf category is included. No sectionwise tensor identification is used.

Searches actually run via `msearch.py NC lem-sfb-relative-tensor-finite-free-coordinates`:

- leanfinder: "Tensoring a finite free internal module over a commutative ring object
  gives a natural finite product isomorphism with relative unitor and coequalizer
  coordinate formulas". Eight hits, including `ModuleCat.FreeMonoidal.μIso`, its
  hom/inverse basis formulas, `ModuleCat.free_μ_freeMk_tmul_freeMk`,
  `FGModuleCat.tensorObj_obj`; none states the internal-module normalized formulas.
- loogle: `"rightDistributor"`. Twelve hits including `rightDistributor`, its
  biproduct projection/inclusion formulas and extensionality lemmas. These are parts
  of the abstract finite-biproduct argument; none includes the relative coequalizer
  and underlying-sheaf normalization clauses together.
- grep: `tensorObjπ|leftUnitor` in `CategoryTheory/Monoidal/Mod.lean`: zero hits.
  The tensor and normalized coequalizer APIs needed here are project extensions.
- leansearch: "Tensoring a finite free module object in abelian sheaves identifies
  the relative tensor naturally with a finite product, with basis projection
  coordinates and normalized unitors". Eight hits including presheaf-module tensor,
  ordinary `Module.Free.tensor`, and `TensorProduct.finsuppLeft`; no exact match.
- Direct `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the item id and proposed declaration names
  found no existing statement. Concept searches for relative finite tensor,
  finite-free tensor, module preadditivity and finite products found the existing
  upstream module tensor/preadditive/limits interfaces and the related
  `CondensedFiniteFreeTensorExact` theorem; none asserts all the requested formulas.
  `rightDistributor` was also inspected directly in Mathlib's monoidal preadditive
  file, including its hom, inverse, and projection signatures.

There is no STATEMENT-DISPUTED issue. Only the main theorem has a postponed proof;
all helper instances apply existing constructions and theorems with real data.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
