## Worker report

The new module `Sheaf.AlgebraicGeometry.FittingIdealSheafPullback` states
`AlgebraicGeometry.Scheme.Modules.fittingIdealSheaf_affine_pullback`, with its whole proof
`sorry`. It introduces no new definitions and changes only the item's `lean` record.
The source is Stacks Divisors, section-fitting-ideals (0C3C),
lemma-base-change-fitting-ideal (0C3D), and lemma-base-change-and-fitting-ideal-omega
(0C3I); the closed-subscheme assertions use Schemes 01JU and Morphisms 01QQ.
These passages were read in `literature/stacks-project/divisors.tex`.

Hypotheses and clauses, in statement order:

- `S : Scheme.{u}` and `F : S.Modules` are the scheme and its structure-sheaf module.
  `[F.IsFiniteType] [F.IsQuasicoherent]` impose precisely finite type and quasi-coherence.
  `r : ℕ` includes index zero. All universes and variables are explicitly bound.
- `fittingIdealSheaf F r` is the dependency's actual largest-ideal construction, without
  introducing a second ideal or assuming the affine bounds are attained.
- `U : S.affineOpens`, `n : ℕ`, and the linear map `π` to `Γ(F, U.1)`, followed by
  `Function.Surjective π →`, quantify over every affine open and every finite generating
  surjection. Its kernel is used inside the existing `π.presentationFittingIdeal r`.
  That definition is the span of all determinants of kernel rows and distinct columns,
  and is definitionally the unit ideal if `n ≤ r`.
- The first equality says `(fittingIdealSheaf F r).ideal U = π.presentationFittingIdeal r`.
  The next equality identifies the restriction as an ideal subsheaf, using `comap U.1.ι`,
  with `ofIdealTop` of that ideal. `U.1.topIso.inv.hom` transports the ideal from
  `Γ(S,U)` to `Γ(U,⊤)`, so it is the associated ideal on the same open subscheme,
  with the inclusion into its structure sheaf retained.
- The first existential is an isomorphism from the inverse image of `U` in the closed
  stratum to `Spec(Γ(S,U)/π.presentationFittingIdeal r)`. Its equation identifies the
  projection to `U` with the quotient map followed by `U.2.isoSpec.inv`. Thus the
  assertion is over `U`, rather than just an abstract isomorphism of schemes.
  The stratum is the existing `.subscheme` with inclusion `.subschemeι`, which has
  Mathlib's `IsClosedImmersion` instance.
- `∀ (T : Scheme.{u}) (h : T ⟶ S)` includes every scheme morphism. The existential
  proofs `hft` and `hqc` conclude finite type and quasi-coherence of the *actual*
  `(tensorPullback h).obj F`; they are not added assumptions. Explicit applications
  `@fittingIdealSheaf ... hft hqc r` use those proofs to type its Fitting ideal, without
  a hidden let/have binder or an auxiliary theorem.
- Equality with `(fittingIdealSheaf F r).comap h` expresses the extended ideal
  `h⁻¹ I · O_T`. The existing affine-extension lemma identifies this encoding with
  extension of ideals on affine pairs; it does not mean the inverse-image module alone.
- The equality of subobjects identifies the inclusion of that Fitting ideal with
  `imageSubobject ((tensorPullback h).map I.toModulesι ≫ ε)`, where `ε` is the adjoint
  of the structure-sheaf map under `tensorPullbackSectionAdjunction h`. This is the
  section-normalized adjunction recorded by the module-pullback dependency, so the
  morphism is canonical. The equality is of subobjects of the structure-sheaf module,
  not of unrelated isomorphic modules; no monicity of the pulled-back map is assumed.
- The final `∃! e` is the canonical isomorphism from the pulled-back module's closed
  stratum to `Limits.pullback h I.subschemeι`. Its equation with `pullback.fst`
  retains the specified immersion over `T`. Uniqueness over `T` is justified by the
  monomorphism property of closed immersions, exactly as in the node's final proof step.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: the existing finite-type and
  quasi-coherence predicates exposed by its public imports. Its conjunction
  `Scheme.Modules.IsQuasiCoherentFiniteType` has the same two hypotheses, written
  separately here for the Fitting-ideal definition's class parameters.
- `Sheaf.AlgebraicGeometry.FittingIdealSheaf`: `Scheme.Modules.fittingIdealSheaf`.
- `Sheaf.RingTheory.PresentationFittingIdeal`: `LinearMap.presentationFittingIdeal`
  and `LinearMap.presentationFittingIdeal_independence_baseChange`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`,
  its instance on `.subschemeι`, and the recorded factorization API
  `IsClosedImmersion.lift` / `lift_fac`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the upstream
  `Scheme.Modules.tensorPullback` and the normalized `tensorPullbackSectionAdjunction`.
  The explicit tensor construction and the full normalized adjunction signature and
  docstrings were read, including its characterization on `1 ⊗ m`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `Limits.pullback`,
  `pullback.fst`, `pullback.snd`. Fully qualifying `Limits.pullback` avoids the distinct
  ordinary-module-pullback functor in the surrounding namespace.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`: `IdealSheafData.comap` and its
  base-change interpretation; `IdealSheafData.ofIdealTop` from Basic;
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`: `toModulesι`.
- Proof-only imports expose every already recorded proof dependency:
  `WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`,
  `Mathlib.AlgebraicGeometry.Modules.Tilde` (`tilde`, `tilde.adjunction`,
  `tilde.toOpen`, and `isIso_fromTildeΓ_of_isQuasicoherent`),
  `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` and `.Basic` (affine gluing and
  `Scheme.Hom.ker`),
  `WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage`
  (`closedSubscheme_baseChange_ideal_image`), and
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine`
  (`IdealSheafData.ideal_comap_appLE`). Those source declarations and docstrings
  were read. The nodes `lem-trf-fitting-ideal-sheaf-affine-sections` and
  `lem-trf-fitting-sheaf-arbitrary-pullback` currently have no Lean declaration to import;
  the docstring retains their role in the proof plan. Neither is required to type this
  statement, so no dependency module or substitute statement was introduced.

Edge cases checked before writing: `r=0`; `n=0` with the zero module; `n≤r` gives
unit ideal and empty quotient stratum; the zero ring and the empty scheme; a free module
of rank `n` gives zero ideal below rank and unit ideal at or above rank. For a nonflat
example take `F=Z/2` on `Spec Z`, `r=0`, and `T=Spec(Z/2)`. The extended ideal and pulled
Fitting ideal are zero, while `(2) ⊗ Z/2` is nonzero. The statement correctly compares
its image with zero and never claims injectivity. Identity morphisms are included.
No finite presentation, Noetherianity, flatness or nonemptiness hypotheses were added.
No statement correction or STATEMENT-DISPUTED fault is needed.

Searches for an existing exact statement (also logged by msearch in searches.jsonl):

- `msearch.py ... leanfinder`: “Fitting ideal sheaves calculated on affine opens commute
  with arbitrary pullback and closed strata base change”. Eight results were general
  `IdealSheafData` affine restriction, map, and subscheme-cover lemmas, not this theorem.
- `msearch.py ... loogle '"fittingIdeal"'`: zero hits.
- `msearch.py ... grep 'Fitting|fittingIdeal' AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py ... leansearch`: “Fitting ideals of finite type quasicoherent modules
  commute with pullback and on affine opens are minors ideals”. Eight results were
  generic ideal-sheaf and sheaf-module pullback lemmas, not the Fitting assertion.
- `rg` in `lean/WeilConjectures` for `fittingIdealSheaf`, Fitting pullback, and the node id,
  and `grep -rn` for the node id: no upstream statement. `rg` in `lean/Sheaf` found
  the existing Fitting construction, local generation theorem, and specialized consumers;
  none states all affine quotient, arbitrary pullback, image, and closed-stratum clauses.
- Exact-name searches in Mathlib, upstream, Sheaf and `dag/lean_names_upstream.json`
  found no pre-existing `fittingIdealSheaf_affine_pullback`.

Validation: scompile.py compiled both the sandbox probe and the library module cleanly
within the 60-second limit (10.8 s and 8.1 s). The initial name-resolution error was fixed
by spelling the scheme fibre products `Limits.pullback`; no mathematical change resulted.
All declaration lines are at most 100 characters and no diagnostic commands remain.

## Second reading by Q55

I reread the node and the final module clause by clause after compilation. This is a
second pass by this worker; no independent sub-agent was started, as the dispatcher brief
forbids it. The maintainer's independent review remains the delivery review.

The check specifically confirmed the direction of `topIso.inv` in the restricted ideal,
the quotient morphism and its composition order, use of the canonical tensor functor
rather than the ordinary pullback functor, and the fact that `hft`/`hqc` are conclusions
and supply only proof parameters to the Fitting construction. The subobject equality
uses the normalized adjoint structure-sheaf morphism and asserts equality of images,
covering the nonflat counterexample above. The final isomorphism is unique over `T`
and retains its immersion. No omitted clause, added hypothesis, hollow construction,
or correction of the node was found. The scheme fibre-product qualification was the
only repair required by the compiler.
