## Worker report

The module `Sheaf.AlgebraicGeometry.AffineModuleCorrespondence` states
`AlgebraicGeometry.Scheme.Modules.affine_module_correspondence`, with one `sorry` and
no definitions. Source read: https://stacks.math.columbia.edu/tag/01SB, including the
Elucidation and the affine tensor calculation in the proof. The local Stacks checkout
is absent on this machine. The node agrees with the source; no correction or dispute.

Hypotheses and objects:

- `universe u`, `{U X : Scheme.{u}}`, `(f : U ⟶ X)` and `[IsAffineHom f]` are the
  two arbitrary schemes and the affine morphism. No finiteness, separation,
  Noetherian, nonempty, or field assumption is imposed.
- Local notation `A` is `TopCat.Sheaf.pushforward CommRingCat f.base` applied to
  `U.sheaf`. Thus its sections are precisely `O_U(f⁻¹ V)`, with their commutative
  ring operations and restrictions. `ρ = ⟨f.c⟩` is `f`'s structure-sheaf map.
- `𝓡` and `𝓻` forget commutativity of ring sheaves/maps solely to use Mathlib's
  `SheafOfModules`. `S` is `SheafOfModules.restrictScalars (𝓻 ρ)`. Thus an
  `A`-module is an actual sheaf of modules over this ring sheaf; its maps are
  `A`-linear, and its underlying `O_X`-module has the stated restricted action.
- `R` is `SheafOfModules.pushforward` along `Opens.map f.base`, using the identity
  of the direct-image ring sheaf. It has exactly the original section modules
  `F(f⁻¹ V)` and the original maps on those sections, without restricting the
  action to `O_X`. `S ⋙ R` is not the intended expression: first `R`, then `S`,
  gives the usual scheme-module pushforward. This latter composite is
  definitionally the right adjoint in `adj₀` (checked by compilation).
- `IsQuasicoherent` is Mathlib's local-presentation definition, on the Zariski
  topology. `QuasicoherentData` consists of a covering family and presentations
  by free modules (arbitrary generator and relation sets). On a topological
  space this is precisely the neighbourhood condition in the node. For scheme
  modules this is the same predicate the recorded coherent module uses, whose
  affine-local tilde characterization is a theorem, not another definition.

Clause (1) is the first conjunct: for every `G : SheafOfModules (𝓡 A)`,
`G.IsQuasicoherent ↔ (S.obj G).IsQuasicoherent`.

Clause (2), including the specified functor, is rendered by the second conjunct
`∀ F : U.Modules, F.IsQuasicoherent → (R.obj F).IsQuasicoherent` and the final
`E : qU.FullSubcategory ≌ qA.FullSubcategory`. Both subcategories are full and
therefore have precisely the linear morphisms of the node. The natural isomorphism
`E.functor ⋙ qA.ι ≅ qU.ι ⋙ R` identifies the equivalence with the actual sectionwise
pushforward, on both objects and maps.

Clause (3), including all its algebra structures and canonical maps:

- `r₀ : f⁻¹ O_X → O_U` is `tensorPullbackRingMap f`.
  `t₀ : f⁻¹ O_X → f⁻¹ A` is the inverse-image ring functor applied to `ρ`.
  The conclusion supplies `B`, `b : O_U → B`, `t : f⁻¹ A → B` with
  `IsPushout r₀ t₀ b t`. This is the tensor-product universal property of the
  commutative ring sheaf `O_U ⊗_(f⁻¹ O_X) f⁻¹ A`, namely `f^* A`. It specifies
  its multiplication and `O_U`-algebra structure, not an arbitrary ring with
  the same underlying module. Pushouts of commutative ring sheaves are the
  sheafification of the sectionwise commutative ring tensor product; no claim
  that their sections are raw tensor products is made.
- `I G` is the recorded `TopCat.Sheaf.inverseImageModule f.base A G`. The
  functor `P` has object `changeOfRings t (I G)` via `pobj`; its map equation
  fixes the maps to `changeOfRingsHom t` of `inverseImageModuleMap`. It is
  therefore `B ⊗_(f⁻¹ A) f⁻¹ G`. Associativity identifies its underlying
  `O_U`-module with `O_U ⊗_(f⁻¹ O_X) f⁻¹ G`. This is precisely the recorded
  `tensorPullback f` of the restricted module, through the natural isomorphism
  `κ : P ⋙ restrictScalars (𝓻 b) ≅ S ⋙ tensorPullback f`.
- The formula for `κ.inv` on `adj₀.unit` says that a local section `g` is
  sent to the sheafification class of `1 ⊗ η(g)`. Together with `O_U`-linearity,
  naturality and locality, this fixes the tensor-associativity identification.
  Under it the action of `B` is `(b ⊗ a)(b' ⊗ g) = bb' ⊗ ag`: it is the
  extension-of-scalars action through `t`, not a freely chosen action.
- `e₀ : f⁻¹ A → O_U` is the ring inverse-image adjoint of `id : A → f_* O_U`.
  The equations `b ≫ ε = id` and `t ≫ ε = e₀` identify `ε : B → O_U` with
  multiplication, hence the tensor-pullback counit `f^* f_* O_U → O_U`.
- `hobj` fixes `H.obj G = changeOfRings ε (P.obj G)`; its map equation fixes
  `H.map` to the sheafified sectionwise tensor map. Thus `H` is exactly the
  formula `f^* G ⊗_(f^* A) O_U`, with `P` retaining the needed algebra action.
  The tensor library places the target-ring factor first, so the displayed
  Lean tensor `1 ⊗ p` is the node's `p ⊗ 1`. This is the existing change-of-rings
  convention of def-pur-sheaf-tensor-product, not a new tensor definition.
- `γ : S ⋙ tensorPullback f ⟶ H` is natural and its section formula, after `κ`,
  is the sheafification of `p ↦ 1 ⊗ p`. The equality transports `pobj` and
  `hobj` only identify the functor objects with the actual tensor objects.
- `α : R ⋙ H ⟶ id` is natural and is pinned by
  `γ.app (R.obj F) ≫ α.app F = adj₀.counit.app F`. It is exactly the map
  induced by the original counit through the tensor quotient.
- `β : id ⟶ H ⋙ R` is an `A`-linear natural transformation, pinned by
  `S.map (β.app G) = adj₀.homEquiv (S.obj G) (H.obj G) (γ.app G)`.
  Thus it is the adjoint of the specified tensor unit, as required.
- `IsIso (α.app F)` and `IsIso (β.app G)` are asserted for every respective
  quasi-coherent module. The conclusion also says `H` preserves quasi-coherence
  and `E.inverse ⋙ qU.ι ≅ qA.ι ⋙ H`, identifying the quasi-inverse functor.

The auxiliary data are existential conclusions, not extra assumptions. They specify
canonical constructions up to their usual natural identifications and keep all
structures and maps in the node. Every operation is already defined generically in
Mathlib or the recorded dependencies; local notations introduce no new notion, so
there is no new definition node or dependency module.

Dependency declarations read and used:

- pqf-def-affine-morphism: `Mathlib.AlgebraicGeometry.Morphisms.Affine`,
  `AlgebraicGeometry.IsAffineHom` (preimages of affine opens are affine).
- def-pc-scheme: `Mathlib.AlgebraicGeometry.Scheme`, `Scheme`, `Scheme.Hom`.
- def-weil-sheaf-of-modules-category: `Mathlib.Algebra.Category.ModuleCat.Sheaf`,
  `SheafOfModules`, `SheafOfModules.Hom`, its category and abelian structure.
- pqf-def-coherent: `Sheaf.AlgebraicGeometry.Coherent`, whose module explicitly
  identifies quasi-coherence with `SheafOfModules.IsQuasicoherent` from
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`; only that clause of
  the dependency is needed, not its coherent predicate.
- def-pc-module-pullback: `Sheaf.AlgebraicGeometry.TensorPullback`,
  `Scheme.Modules.tensorPullback`, `tensorPullbackRingMap`; the explicit
  inverse image is the imported `Sheaf.Topology.InverseImageModule`.
- def-pur-sheaf-tensor-product:
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`,
  `SheafOfModules.changeOfRings`, `changeOfRingsPresheaf`, `changeOfRingsHom`.
- Added landed statement dependency lem-pc-module-pullback-adjunction:
  `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`,
  `Scheme.Modules.exists_tensorPullbackAdjunction`. This pins `adj₀` to the
  canonical tensor unit, rather than an arbitrary adjunction. Its whole
  signature/docstring and record were read. It is already on sheaf-dag;
  the standing brief permits adding a landed statement dependency.

Edge cases checked: empty source and/or target (no nonemptiness assumption);
zero module and zero section rings; identity and empty affine morphisms;
unbounded generator/relation sets in the local presentations; non-Noetherian
schemes; arbitrary scheme universe `u`. All sheaf, algebra, module and index
universes use the common scheme universe, as the dependency declarations do.
No characteristic or finite-presentation hypothesis has entered the statement.

Searches made before writing (all msearch calls recorded in searches.jsonl):

- msearch leansearch, `equivalence quasi coherent modules affine morphism pushforward algebra`:
  unavailable (HTTP Internal Server Error), recorded as unavailable, no verdict.
- msearch leanfinder, `quasicoherent modules equivalence affine morphism pushforward structure sheaf algebra`:
  eight hits, including the generic `Scheme.Modules.pushforward` and ordinary
  pullback adjunction, and affine-site equivalences; none is this theorem.
- msearch loogle, `SheafOfModules.pushforward`: generic pushforward, congruence,
  composition, and over-site operations; no affine quasi-coherent correspondence.
- msearch grep, `affine.*equiv|equiv.*affine|def pushforward|def restrictScalars`
  in Mathlib/AlgebraicGeometry: affine-scheme/ring and affine-site equivalences,
  but no module correspondence.
- rg in Mathlib/AlgebraicGeometry/Modules for quasi-coherent names: tilde and its
  affine global-sections equivalence, restriction along open immersions, and
  a TODO about affine pushforward; none states the node.
- rg in WeilConjectures/AlgebraicGeometry and lean/Sheaf/AlgebraicGeometry for
  affine module, quasi-coherent algebra, pushforward algebra and scalar restriction:
  affine-section, tensor and descent lemmas; no correspondence theorem.
- rg for the item id in WeilConjectures and dag/lean_names_upstream.json:
  no attached declaration. rg for `affine_module_correspondence` in Mathlib,
  WeilConjectures and lean/Sheaf: no prior declaration with this name.
- Read the generic sheaf pushforward/restriction, quasicoherent presentations,
  inverse-image and tensor/change-of-rings definitions directly. `IsPushout`
  is the existing category-theoretic universal property, not a private tensor.

Validation: server single-file compile succeeded with exit code 0 and no warnings.
The delivery dry run printed OK: compilation and preflight pass except for the
independent second reading, which the next worker writes. Nothing was pushed.

## Second reading by K1

Source checked: Stacks Project, Morphisms, Lemma 01SB (tag 01SB), including the
Elucidation and the affine tensor calculation. The source says: for an affine
morphism `u : U ⟶ X`, with `A = u_* O_U`, (1) an `A`-module is quasi-coherent
iff its underlying `O_X`-module is; (2) pushforward sends quasi-coherent
`O_U`-modules to quasi-coherent `A`-modules and is an equivalence with the
specified linear morphisms; (3) the quasi-inverse is
`u^*G ⊗_{u^*A} O_U`, with its algebra/module actions and the counit-induced
natural maps, both isomorphisms.

Object and hypothesis matching:

- `f : U ⟶ X` in the Lean theorem is the source `u`, with the same arbitrary
  schemes in one universe and the sole hypothesis `[IsAffineHom f]`; there are
  no added finiteness, separation, Noetherian, characteristic, or nonemptiness
  assumptions.
- `A`, `ρ`, `𝓡`, `𝓻`, `S`, and `R` are the direct-image commutative ring sheaf,
  structure-sheaf map, ring-category forgetful maps, scalar restriction, and
  sectionwise pushforward algebra-module functor described by the source.
- `qU` and `qA` are the full subcategories of quasi-coherent `O_U`-modules and
  quasi-coherent `A`-modules. `I`, `r₀`, `t₀`, `e₀`, and `adj₀` render inverse
  image, tensor-pullback maps, the counit, and the recorded canonical
  tensor-pullback adjunction.

Conclusion matching:

- The first conjunct is exactly clause (1), with `G.IsQuasicoherent` as
  quasi-coherence over `A` and `S.obj G` as the underlying `O_X`-module.
- The second conjunct is exactly the clause that every quasi-coherent `F` has
  quasi-coherent pushforward. The existential equivalence `E` has precisely the
  two full quasi-coherent categories and the natural isomorphism identifying
  its functor with `R`.
- The third conjunct supplies the pushout algebra `B = u^*A`, its maps and
  multiplication counit; `P` is extension of scalars giving `u^*G`; `κ`
  states the tensor-pullback identification and its section formula; `H` is
  change of rings along the counit and preserves quasi-coherence; `γ` is the
  canonical `p ↦ 1 ⊗ p` map; `α` is the counit-induced map and `β` its adjoint.
  The displayed map equations fix the functor maps, and the `IsIso` clauses
  assert exactly the two source isomorphisms on the indicated module types.
  The final natural isomorphism identifies the inverse equivalence with `H`.
  Quantifier order and all algebra/module actions agree with the node.

Edge cases checked: empty schemes and empty affine opens, zero rings and zero
modules, identity and empty affine morphisms, arbitrary (possibly empty)
generator and relation index sets, non-Noetherian schemes, and `n = 0`-type
situations are all admitted. No characteristic or finite-presentation condition
is introduced, and all scheme/sheaf/index universes are tied to `u`.

Searches: `rg` over the repository and the slopmaster2 source for
`affine_module_correspondence`, affine module equivalences, and quasi-coherent
pushforward found no prior declaration. Mathlib searches (LeanSearch,
LeanFinder, Loogle, and direct `rg`) found only generic sheaf pushforward,
restriction, affine-spectrum, and tilde equivalences, not this relative
correspondence. The dependency declarations and their source files were read;
`exists_tensorPullbackAdjunction` is the recorded canonical adjunction used by
`adj₀`.

Mismatch found and repaired: the Lean signature uses
`exists_tensorPullbackAdjunction`, so `lem-pc-module-pullback-adjunction` was
added to the item's `stmt_deps` in the sandbox node copy. No statement clause,
hypothesis, definition, or proof text required correction. The module compiled
with `scompile.py` (exit code 0, no warnings except the permitted `sorry`).
