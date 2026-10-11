## Worker report

The main module is `Sheaf.AlgebraicGeometry.AffinePushforwardBaseChange`, in namespace
`AlgebraicGeometry.Scheme.Modules`. Its four sorry-only theorems state all three clauses
and the affine-local identification of the item. A dependency module states the structure
sheaf pullback assertion for the recorded tensor pullback (see below). No definitions,
private copies, new nodes, statement corrections, or proved lemmas were introduced.

Source read: https://stacks.math.columbia.edu/tag/02KG (Lemma 30.5.1, statement and proof).
The local `literature/stacks-project/coherent.tex` is absent on this machine; the official
Stacks page supplies the text. It gives affine pushforward quasi-coherence and base change,
and explicitly reduces the assertion to the nested tensor identity. Clauses (2) and (3)
are the additional consequences written in the node, not claims that Stacks 02KG itself
states these clauses. The six proof steps of the node are carried in the theorem docstrings.

Hypotheses and clauses:

- Schemes X, S, X', S' are `{X S X' S' : Scheme.{u}}`. All four maps in the node are
  explicit binders `f`, `f'`, `g`, `g'` with exactly those domains and codomains.
- The fibre product with these projections is `sq : IsPullback g' f' f g`. This is
  the universal-property form of `def-pc-fibre-product`; it allows any chosen fibre
  product, rather than requiring equality with Mathlib's particular chosen object.
  `sq.w` supplies the commutativity proof used by the canonical base change map.
- Affineness is `[IsAffineHom f]`, the exact Mathlib match of pqf-def-affine-morphism.
- An O_X-module is `F : X.Modules`, definitionally the scheme's `SheafOfModules`.
  Quasi-coherence is `[F.IsQuasicoherent]`. The Coherent dependency's module docstring
  explicitly identifies this clause of its node with Mathlib's existing predicate;
  its named `RingedSpace.IsCoherent` is the separate coherent clause and is not substituted
  for quasi-coherence here.
- Clause (1), quasi-coherence of the pushforward, is
  `((pushforward f).obj F).IsQuasicoherent` in `affinePushforward_baseChange`.
- Clause (1), invertibility of the specified map, is
  `IsIso (moduleBaseChangeMap f f' g g' sq.w F)`. This is C1's existing map, defined by
  the Hom equivalence of the pinned tensor pullback adjunction from the pushforward
  of the top-arrow unit. Thus an arbitrary isomorphism between the two objects does
  not replace the specified map.
- The affine-local formula is `affinePushforward_baseChange_affine_formula`.
  It quantifies over arbitrary commutative R, B, R' and their specified R-algebras,
  and arbitrary `M : ModuleCat B`. The ring maps on the square of spectra are the
  two algebra maps and the two tensor factor inclusions. In particular, the explicit
  `Algebra.TensorProduct.rightAlgebra` gives B's action on R' tensor B through the
  right inclusion, not an unrelated action. The restricted R-action on M is explicitly
  `Module.compHom M (algebraMap R B)`.
  The `R'`-linear equivalences `a` and `b` identify the sections of the two sides with
  `R' ⊗[R] M` and `(R' ⊗[R] B) ⊗[B] M`. Their first two equations pin their inverses
  on generators by the canonical units and `tilde.toOpen`. `1 tensor m` generates the
  first tensor module as an R'-module; `(1 tensor z) tensor m` generates the second.
  The last equation explicitly asserts that the actual beta sends `r tensor m` to
  `(r tensor 1) tensor m`, including all r and m. This gives the precise identification,
  not merely an abstract isomorphism between tensor modules.
  Every affine open in the node is a scheme in its own right. Apply this spectrum
  assertion to the restricted square and use the affine tilde-Gamma identifications
  and the already landed open-restriction comparison. Thus the spectrum normal form
  renders the formula on all affine opens, for arbitrary quasi-coherent F (each such
  restriction is the tilde of its sections), without adding an affine hypothesis to
  the global statement.
- Clause (2) is `affinePushforward_baseChange_algebra`. `A` and `A'` are exactly the
  pushforwards of `SheafOfModules.unit` on X and X'. The term `epsilon k` is the
  adjoint of `unitToPushforwardObjUnit k.toRingCatSheafHom` under the canonical
  tensor pullback adjunction. `gamma` is beta for O_X followed by `pushforward f'`
  of this precise epsilon for g'.
  The existential `mu` and `mu'` are characterized on tensor sections on EVERY open
  by multiplication of structure-sheaf sections. These equations specify the actual
  canonical multiplications; no unconstrained algebra structure is assumed.
  `IsIso gamma` states invertibility of its underlying module map. The next equality
  is multiplication compatibility through the tensor comparison selected from the
  recorded `module_pullback_tensor g`. The final equality is unit compatibility with
  the structure maps f-sharp and f'-sharp through epsilon_g. An invertible module map
  respecting these two operations is exactly an algebra isomorphism (its inverse
  respects them as well); no separate bundled algebra category is needed.
- Clause (3) is `affinePushforward_baseChange_comp`. It binds the further schemes and
  maps h, h', f'', and `sq₂ : IsPullback h' f'' f' h`, besides the original cartesian
  square, affineness and quasi-coherence. Its conclusion equates the outer canonical
  beta to the four-arrow composite, with the two explicit composition comparisons
  obtained by conjugating `pushforwardComp` under the same canonical adjunctions.
  The commutativity proof of the rectangle is written from `sq₁.w` and `sq₂.w`.
  Cartesian pasting (`IsPullback.paste_vert_iff`) identifies its source with the
  iterated fibre product of the node. There is no arbitrary comparison isomorphism.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Morphisms.Affine: `AlgebraicGeometry.IsAffineHom`.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: `pullback`, its projections
  and universal property; Mathlib's `CategoryTheory.IsPullback` expresses the same
  universal property with arbitrary specified projections.
- Sheaf.AlgebraicGeometry.Coherent: its docstring identifies quasi-coherence with
  `SheafOfModules.IsQuasicoherent` (Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent).
- Sheaf.AlgebraicGeometry.TensorPullback: `Scheme.Modules.tensorPullback`, its explicit
  tensor data and composition assertion.
- Mathlib.Algebra.Category.ModuleCat.Sheaf: `SheafOfModules`, its module morphisms/category.
- Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree: `unitToPushforwardObjUnit` and
  the Mathlib `pullbackObjUnitToUnit` signatures; the latter is for a different
  implementation of pullback, necessitating the dependency module below.
- Sheaf.AlgebraicGeometry.ModulePullbackTensor: `module_pullback_tensor`, including
  naturality and the unit formula on elementary tensor sections.
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic: `IsPullback.paste_vert_iff`.
- Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction: `moduleBaseChangeMap`,
  its full definition by adjunction, naturality and open-restriction comparison.
- Sheaf.AlgebraicGeometry.TensorPullbackAdjunction: `exists_tensorPullbackAdjunction`,
  including its unit's formula. The preceding two landed nodes were added to stmt_deps
  to cite the particular map and adjunction appearing in the signatures.
- Mathlib.AlgebraicGeometry.Modules.Tilde: `tilde`, `tilde.toOpen`, `moduleSpecΓFunctor`.
  Mathlib.RingTheory.TensorProduct.Basic: `Algebra.TensorProduct.rightAlgebra`.

Edge cases checked before writing: empty schemes are allowed by the general Scheme binders
and universal-property squares; zero rings are allowed by CommRing (no Nontrivial assumption);
zero modules are allowed, and the displayed tensor maps identify zero modules; identity base
changes and identity further maps are allowed, with the canonical composition comparisons;
arbitrary nonflat/non-finite-type g and h are allowed. No field, Noetherian, separated, finite
presentation, flatness or characteristic hypothesis was introduced. All rings/schemes and
module carriers share u, as in the library's `Scheme.Modules` convention; any such data can
be lifted to a common universe. No independent test-object universe or index restriction is
introduced. Variables and universes are explicitly bound, with autoImplicit disabled.

Searches (2026-10-11):

- msearch.py leanfinder, query `pushforward of quasi-coherent modules along an affine
  morphism commutes with arbitrary base change`: eight hits, including pushforward,
  pushforwardComp and pullbackPushforwardAdjunction; none state the affine base change theorem.
- msearch.py loogle, query `AlgebraicGeometry.Scheme.Modules.pushforward,
  AlgebraicGeometry.IsAffineHom`: zero hits.
- msearch.py leansearch, query `affine base change quasi coherent sheaf pushforward`:
  unavailable (Internal Server Error). Used LeanFinder, Loogle and local grep as fallbacks.
- msearch.py grep `baseChange|base_change` in Mathlib/AlgebraicGeometry/Modules: zero hits.
- rg in source WeilConjectures/Mathlib/AlgebraicGeometry/Modules and the project's
  lean/Sheaf/AlgebraicGeometry for baseChange, tensorPullback/Unit and algebra/multiplication:
  found canonical moduleBaseChangeMap and pasting, the tensor comparison, and Mathlib
  pullbackObjUnitIso; no affine pushforward base change or tensor-pullback structure theorem.
- rg of the item id in WeilConjectures: no occurrence.
- rg `affinePushforward|isIso_tensorPullback_structureSheaf` throughout Mathlib,
  WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json: no collisions.

Validation: the two modules compile together on the server, dependency first, in 4.2 seconds,
exit code 0, no warnings. All five theorem bodies are exactly `by sorry`.
No STATEMENT-DISPUTED issue was found; the item statement is unchanged.

## Dependency modules

`lem-weil-pbc-module-pullback-structure-sheaf` has a Mathlib match for Mathlib's
`Scheme.Modules.pullback`. The project's `def-pc-module-pullback` instead records the
explicit tensor pullback, and the pinned canonical adjunction is supplied by
`exists_tensorPullbackAdjunction`. `Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf`
states `isIso_tensorPullback_structureSheaf` for precisely the adjoint of the existing
`unitToPushforwardObjUnit` under this adjunction. It supplies the dependency's full assertion
for the required pullback: the epsilon is specified, its defining adjunction equation and
section formula are inherent in the homEquiv construction, and the theorem asserts it is an
isomorphism. Its docstring gives the tensor-balancing proof and source Tags 0095/0096/01BG.
Only this dependency node's `lean` field is changed, with the required explanatory note;
its statement, source and Mathlib match are preserved.

## Second reading by F1

I reread the node statement, its Stacks source (Cohomology of Schemes, Lemma 02KG and
Remark 0ATM for composition), every recorded dependency signature, and both delivered
modules. The object and hypothesis matching is as follows.

- The four schemes `{X S X' S' : Scheme.{u}}`, maps `f`, `f'`, `g`, `g'`, and the
  universal-property square `sq : IsPullback g' f' f g` are rendered verbatim by
  `affinePushforward_baseChange`; no chosen pullback object or equality is imposed.
- Affineness is exactly `[IsAffineHom f]`; the module is `F : X.Modules` with exactly
  `[F.IsQuasicoherent]`. No Noetherian, separated, finite-type, flatness, field,
  characteristic, or nontriviality hypothesis is added.
- Clause (1)'s two conclusions are rendered by the conjunction
  `((pushforward f).obj F).IsQuasicoherent` and
  `IsIso (moduleBaseChangeMap f f' g g' sq.w F)`. The map is the recorded canonical
  module-base-change map, including the supplied commutativity proof.
- The affine-local identification in the node is rendered by
  `affinePushforward_baseChange_affine_formula`: arbitrary commutative rings and
  algebras, `M : ModuleCat B`, the restricted `R`-action, the tensor-product right
  `B`-algebra, the four spectrum maps, the commutativity witness, the two pinned
  `R'`-linear equivalences, their generator equations, and the equation sending
  `r ⊗ m` to `(r ⊗ 1) ⊗ m`.
- Clause (2) is rendered by `affinePushforward_baseChange_algebra`. Its `A`, `A'`,
  epsilon, and gamma are the canonical pushforwards and adjoint map from the node;
  multiplication and unit are specified on every open by section multiplication,
  and the tensor comparison is exactly `module_pullback_tensor`. The existential
  algebra operations, `IsIso gamma`, multiplication equality, and unit equality
  match the node's clauses.
- Clause (3) is rendered by `affinePushforward_baseChange_comp`, with the further
  schemes and maps, both pullback squares, the same affineness and quasi-coherence
  hypotheses, the pasted rectangle commutativity proof, and the exact composite of
  the two base-change maps conjugated by the canonical pullback/pushforward
  composition comparisons.

No mismatch was found and no repair was needed. In particular, no arbitrary
isomorphism replaces the specified base-change map, and no unconstrained algebra
structure replaces the canonical operations. The dependency module
`TensorPullbackStructureSheaf.lean` states the dependency node's tensor-pullback
(not Mathlib's separate `Scheme.Modules.pullback`) assertion and uses the pinned
`exists_tensorPullbackAdjunction` and `unitToPushforwardObjUnit`.

Edge cases checked: empty schemes and identity maps are admitted by unrestricted
`Scheme` binders and `IsPullback`; zero rings and zero modules are admitted by the
`CommRing` and `ModuleCat` hypotheses; `R'`, `B`, and `M` in the affine formula are
arbitrary; no characteristic or positive-dimension assumption occurs; and all
scheme, ring, and module universes are the shared `u`, with no vacuous independent
index or test-object universe.

Searches were rechecked with `msearch.py` (LeanFinder, Loogle, and LeanSearch
fallback), `rg` in Mathlib, `WeilConjectures`, and this repository, for
`affinePushforward`, affine pushforward/base-change, and tensor-pullback structure
sheaf. They found only the existing adjunction, tensor comparison, pushforward,
and base-change-map infrastructure; no declaration of this theorem. The recorded
Mathlib match for the dependency uses the different `Scheme.Modules.pullback`, so
the delivered dependency module is required and is used.

## Reviewer fix (R-apb1225)

lem-weil-pbc-module-pullback-structure-sheaf had already landed (E1 071314dbf, `tensorPullbackObjUnitToUnit` / `tensorPullbackObjUnitToUnit_isIso` in Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf): the delivered re-record and its duplicate module were reverted, and the `epsilon` of clause (2) is now the landed `tensorPullbackObjUnitToUnit` (one definition per notion). The `let` binders of the affine-formula and algebra statements (f, g, f', g', A, A', epsilon, gamma) were inlined; the instance `letI`s stay.
