## Worker report

The module `Sheaf.AlgebraicGeometry.AffineTruncationKernelFiniteLocallyFree` states
`AlgebraicGeometry.affine_truncationKernel_finiteLocallyFree`, with proof `sorry`.
It creates no definitions and proves no mathematical lemma. The compiler reports no errors
or warnings (server compile: 11.8 seconds).

Clause-by-clause correspondence:

- `A : Type u` and `[CommRing A]` give the affine scheme `Spec (.of A)`. No Noetherian,
  reducedness, domain, or nonzero-ring assumption is imposed.
- `U : (Spec (.of A)).Opens` is the open subscheme; `hU : IsCompact (U : Set ...)` is its
  quasi-compactness.
- `P : CochainComplex (ModuleCat.{u} A) ℤ` is the module complex. `hbounded` says that
  its terms above some integer N are zero, and `hfree` says every term is both free
  and finitely generated over A. This is bounded above, not bounded on both sides.
- `E : schemeDerivedCategory U.toScheme` is the object in D(O_U), and
  `hperfect : Scheme.IsPerfect U.toScheme E` is precisely the recorded perfectness notion.
  The `HasDerivedCategory` binders provide the shared derived-category constructions
  on U and on its localized open sites; they impose no geometric hypothesis.
- `hrep` says the termwise associated sheaf complex of P, restricted to U, is isomorphic
  to E after applying `DerivedCategory.Q`. The functor in this term is the composite of
  `tilde.functor`, `SheafOfModules.overFunctor`, and the functor of
  `Scheme.Modules.overEquiv U`. The explicit `@id` only selects the shared raw
  SheafOfModules category instead of the definitionally equal Scheme.Modules carrier
  with its separately named category instance. It introduces no new notion or assumption.
- Integers `a b`, `hab : a ≤ b` and `htor` express the Tor-amplitude interval [a,b].
  `htor` quantifies over ALL O_U-module sheaves G, not just quasi-coherent sheaves,
  and says `schemeDerivedTensorCohomologyVanishes U.toScheme E G i` for i<a or b<i.
  This is the sheaf-side amplitude formula used by `affine_torAmplitude_iff`.
- `r : ℤ`, `hr : r < a` are arbitrary, not an existential choice or the weaker r≤a.
- K is `image (P.d (r - 1) r)` in ModuleCat A. This is the categorical image module,
  canonically the ordinary image submodule, with inclusion `image.ι`. The same
  tilde/open-restriction composite applied to it is the sheaf tilde(K)|U.
- The first conclusion is an isomorphism e from this restricted sheaf to the kernel
  of the restricted next differential. The equation
  `e.hom ≫ kernel.ι ... = (...).map (image.ι ...)` identifies the inclusions in the
  restricted degree-r term. Thus the assertion is equality as subobjects, not merely
  an unrelated abstract isomorphism. It asserts no image/kernel equality on X.
- The remaining three conjuncts are, respectively, `SheafOfModules.IsFlat`,
  `SheafOfModules.IsFinitePresentation`, and `SheafOfModules.IsFiniteLocallyFree.{u,u,u}`
  of exactly this same restricted associated image sheaf. Finite local freeness allows
  the rank to vary, and does not assert a globally constant rank.

Dependencies and declarations inspected and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`; its full structure
  is a locally ringed space with local affine presentations. `Spec` is used literally.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `AlgebraicGeometry.schemeDerivedCategory`.
- `Sheaf.AlgebraicGeometry.PerfectComplex`: `AlgebraicGeometry.Scheme.IsPerfect`,
  including its full local strictly-perfect-model definition and derived-category binders.
- `Sheaf.AlgebraicGeometry.AffineTorAmplitudeCriterion`:
  `AlgebraicGeometry.affine_torAmplitude_iff`. Its sheaf-side formula uses
  `AlgebraicGeometry.schemeDerivedTensorCohomologyVanishes` from
  `Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes`, reused verbatim here.
  The criterion itself is a future proof ingredient, not an additional hypothesis.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat`: `SheafOfModules.IsFlat`, the exactness
  of right tensoring by the sheaf, carried by `def-pc-flat-sheaf-modules`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFree`, the existing varying-rank notion carried by
  `def-sc-finite-locally-free-sheaf`. Its full signature and local-generators field were read.
- Mathlib `SheafOfModules.IsFinitePresentation` (ModuleCat/Sheaf/Quasicoherent.lean:267)
  means locally a cokernel of a map between finite free sheaves; its docstring and field
  were read. Mathlib's `image`, `image.ι`, `kernel`, `kernel.ι`, and termwise
  `Functor.mapHomologicalComplex` supply all remaining constructions.
- The original `def-pc-finite-locally-free` record was read at
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`, including both
  `Scheme.Hom.IsFiniteLocallyFree` and `Scheme.Hom.IsFiniteLocallyFreeOfDegree`.
  They concern scheme morphisms and cannot express the sheaf conclusion. The reference
  correction below replaces this dependency, rather than redefining either notion.

The existing local attributes enable Mathlib's additivity-from-finite-product-preservation
and finite-limit/colimit composite instances. They declare no new data. The short `by simp`
inside `hrep` supplies zero preservation of the already defined functor, not a new theorem.
No file-local notation, local instance declaration, private abbreviation, or let binder occurs.
Universes `u w` are explicitly bound and `autoImplicit` is disabled.

Edge cases checked mathematically: U may be empty (all restricted sheaves are zero),
A may be the zero ring (empty spectrum), P and E may be zero, the free rank may be zero,
and ranks may vary on disconnected U. There is no lower term bound on P and no
assumption that the complex is exact away from U. The strict inequality r<a is needed;
at r=a the kernel/image comparison can fail. Finite presentation is justified on U by
exactness one degree earlier, identifying K locally with the cokernel of the preceding
map between finite free modules; it is not asserted globally over A. No statement is disputed.

Searches for existing declarations (all service searches via msearch.py):

- LeanSearch: `image below Tor amplitude bounded above finite free complex finite locally free on open`:
  unavailable, HTTP Internal Server Error, recorded in searches.jsonl.
- LeanFinder, same query: eight generic derived-category truncation/support hits, including
  `DerivedCategory.isGE_Q_obj_iff` and `exists_iso_Q_obj_of_isGE_of_isLE`; no matching theorem.
- Loogle: `Module.Flat, Module.FinitePresentation`: six hits, including
  `Module.Flat.projective_of_finitePresentation` (Tag 00NX), but no theorem involving a
  restricted affine complex and its image/kernel.
- Mathlib grep: `truncation.*(flat|free)|syzygy.*flat`: three unrelated simplicial-set hits.
- `rg` on WeilConjectures and lean/Sheaf for truncation/free/flat, syzygy, and the node id:
  only unrelated syzygy statements and mentions of the proposed theorem in the already
  landed AffinePerfectPlusLocallyFree docstring. No existing statement of this node.
- `rg` for the proposed full/short declaration name in Mathlib, WeilConjectures,
  dag/lean_names_upstream.json, and lean/Sheaf: no collisions.
- DAG search for sheaf finite-locally-free and `SheafOfModules.IsFlat` records found the
  existing nodes named above; no new definition node or dependency module is needed.

Source check: local literature/stacks-project/perfect.tex is absent on this machine.
Read https://stacks.math.columbia.edu/tag/08ED and
https://stacks.math.columbia.edu/tag/08EG directly. Tag 08ED is essential surjectivity
of restriction, not the quoted truncation argument. Tag 08EG, proof of Lemma 36.13.6,
contains precisely this argument. The Lean docstring uses the correct tag and records
that the DAG's source is miscited; its maintainer-owned source field is left intact.

## Statement corrected

The mathematical assertion is unchanged. Its final definition reference originally pointed
to a predicate on scheme morphisms; it now points to the existing variable-rank sheaf
predicate `def-sc-finite-locally-free-sheaf`. The existing sheaf-flatness definition
`def-pc-flat-sheaf-modules` is also cited explicitly. The corresponding stmt_deps change
removes the morphism-only definition and adds these two sheaf definitions. Proof and
proof_deps are unchanged. The statement_change record includes the original statement
verbatim, the original stmt_deps, and every citer found by scanning both dependency fields.

Citer `lem-sc-affine-perfect-plus-locally-free`: holds true. It uses exactly the same
restricted image sheaf as the finite locally free summand; changing the definition
references does not affect that application. It is the only citer in stmt_deps/proof_deps.
The item is not a blueprint unit statement (blueprint.is is null).

The correction follows Stacks Tag 08EG, proof of Lemma 36.13.6, the paragraphs defining K,
proving flatness and concluding finite local freeness (the original source calls it 08ED).

## Second reading by E1

I reread the node, its corrected dependency list, the Lean module, and Stacks Tag 08EG
(Lemma 36.13.6). The source states: affine X = Spec(A); quasi-compact open U; perfect
E on U; a bounded-above finite-free lift; a Tor-amplitude interval [a,b]; and, for every
r<a, K = Im(P^(r-1) -> P^r), with K|U identified with Ker(P^r|U -> P^(r+1)|U), flat,
of finite presentation, and finite locally free. The Lean renders these items as follows.

- `A : Type u`, `[CommRing A]`, and `U : (Spec (.of A)).Opens` render X and its open;
  `hU : IsCompact (U : Set (Spec (.of A)))` is exactly quasi-compactness.
- `P : CochainComplex (ModuleCat A) ℤ`, `hbounded`, and `hfree` render a bounded-above
  complex whose every term is finite free. No Noetherian, domain, reduced, or nonzero-ring
  hypothesis is added.
- `E : schemeDerivedCategory U.toScheme`, `hperfect`, and `hrep` render the perfect
  derived object and the restricted sheafified complex representing it. The two derived
  category instance binders are construction data, not geometric assumptions.
- `a b`, `hab : a ≤ b`, and `htor` render Tor amplitude [a,b], with quantification over
  every sheaf of modules and every integer outside the interval. `r` and `hr : r < a`
  render the arbitrary lower degree required by the source.
- The conclusion uses `image (P.d (r - 1) r)` and the same explicit tilde/open-equivalence
  functor throughout. Its existential isomorphism to `kernel (map (P.d r (r+1)))`, together
  with the displayed equation through `kernel.ι` and `image.ι`, is the asserted
  inclusion-compatible equality after restriction to U. The remaining conjuncts are
  `SheafOfModules.IsFlat`, `IsFinitePresentation`, and varying-rank
  `IsFiniteLocallyFree` for that same restricted image sheaf.

The empty open, zero ring, zero complex, zero object, rank-zero sheaf, disconnected U,
and all integer choices including `a = b` and `r < a` are admitted. No lower bound on P,
constant-rank condition, or equality on all of X is imposed. Universes are explicitly
  bound; the sheaf and scheme universes agree and the derived-category universe is
  independent as in the dependency declarations.

Searches were reread: LeanSearch was unavailable (recorded as unavailable), LeanFinder
returned only generic projective-dimension declarations, Loogle returned no match, and
grep over Mathlib, WeilConjectures, and `lean/Sheaf` found no truncation-kernel theorem or
duplicate declaration. The recorded definitions were opened: `Scheme.IsPerfect`,
`schemeDerivedCategory`, `affine_torAmplitude_iff`, `SheafOfModules.IsFlat`, and
`SheafOfModules.IsFiniteLocallyFree`; all are the notions used by the module.

One mismatch was found and is repaired in this delivery: the old statement cited
`def-pc-finite-locally-free`, whose declaration is a property of scheme morphisms
(`Scheme.Hom.IsFiniteLocallyFree`), for the sheaf conclusion. The corrected statement
and `stmt_deps` cite the existing sheaf predicate `def-sc-finite-locally-free-sheaf` and
the existing sheaf-flatness predicate `def-pc-flat-sheaf-modules`; no mathematical clause
was changed. The sole citer, `lem-sc-affine-perfect-plus-locally-free`, still applies
verbatim (`holds: true`). The module compiles cleanly with its proof left as `sorry`.
